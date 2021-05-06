(ns balancer.core
  (:require [spork.opt.dumbanneal :as da]
            [spork.opt.annealing :as ann]
            [spork.util [table :as tbl]]
            [clojure.core.logic :refer :all :as l]
            [clojure.core.logic.fd :as fd]))

(def src-data
  (into {}
        (for [[src xs]  (->> (tbl/tabdelimited->records "data.csv")
                             (into [])
                             (group-by :SRC))]
          [src {:STR        (-> xs first :STR)
                :quantities (into {} (mapv #(vector (:Qty %) (select-keys % [:Score :Excess])) xs))}])))

;;Our solution will be a set of SRCs

(def srcs (keys src-data))

(defn choices [src]
  (let [d (src-data src)
        str (:STR d)]
    (->> (for [[q m] (d :quantities)]
           [q (merge {:total-strength (* q str)} m)])
         (into {}))))

(defn score  [src qty]   (-> src choices (get qty) :Score))
(defn excess [src qty]   (-> src choices (get qty) :Excess))
(defn src-strength [src qty]  (-> src src-data :STR (* qty)))

;;a solution is just a map of
;;{:choices src->quantity :total-strength n}

(defn total-strength [src-data src->quantity]
  (->> src->quantity
       (map (fn [[src n]] (* (-> src src-data :STR) n)))
       (reduce +)))

;;objectives...
(defn strength-deviation [sol]
  (- (sol :target) (sol :total-strength)))

(defn total-fill-scores [choices src-data]
  (let [[score excess] (->> (keys choices)
                            (map #(-> % src-data :quantities (get (choices %))))
                            (reduce (fn [[score excess] {:keys [Score Excess]}]
                                      [(+ score Score) (+ excess Excess)])
                                    [0 0]))]
    {:score score :excess excess}))

(defn incremental-cost [{:keys [choices src-data]} src old-choice new-choice]
  (let [src-info   (-> src src-data)
        str        (src-info :STR)
        old-scores (-> :quantities src-info (get old-choice))
        new-scores (-> :quantities src-info (get new-choice))]
    {:score  (-  (new-scores :Score)  (old-scores :Score) )
     :excess (-  (new-scores :Excess) (old-scores :Excess))
     :str    (* (-  new-choice old-choice) str)}))

(defn random-choice [{:keys [choices variables src-data] :as sol}]
  (let [src        (rand-nth variables)
        qty        (choices src)
        neighbors  (-> src src-data :quantities)
        n          (rand-nth (keys (dissoc neighbors qty)))]
    [src n (incremental-cost sol src qty n)]))

(defn incremental-cost->total-cost
  [{:keys [total-score total-excess total-strength target] :as sol} [src n cost]]
  (let [{:keys [score excess str]} cost]
    {:total-score    (+ score total-score)
     :total-excess   (+ total-excess excess)
     :total-strength (+ total-strength  str)}))

(defn random-move [sol]
  (let [[src n _ :as mv] (random-choice sol)
        new-info (incremental-cost->total-cost sol mv)]
    (-> sol
        (merge new-info)
        (assoc-in [:choices src] n))))

(defn cost-info [sol]
  (select-keys sol [:total-score :total-excess :total-strength]))


;;not really used at the moment, but CLP stuff for definining solutions.
(defn var-bounds [sd]
  (into {}
    (for [[src {:keys [quantities STR]}] sd]
      (let [qs (sort (keys quantities))]
        [src {:var (lvar) :lower  (first qs) :upper (last qs) :STR STR}]))))


;;smart packing using finite domain constraints.
(defn productsumo [vars dens sum]
  (fresh [vhead vtail dhead dtail product run-sum]
    (conde
     [(emptyo vars) (== sum 0)]
     [(conso vhead vtail vars)
      (conso dhead dtail dens)
      (fd/* vhead dhead product)
      (fd/+ product run-sum sum)
      (productsumo vtail dtail run-sum)])))

(defn pack [src-data amount]
  (let [src->bounds (var-bounds src-data)
        src->var (reduce-kv (fn [acc src m]
                              (assoc acc src (m :var))) {} src->bounds)
        vars      (vals src->var)
        srcs      (keys src->var)
        var->src  (zipmap  vars srcs)
        var-info  (reduce-kv (fn [acc src m]
                              (assoc acc (m :var) m)) {} src->bounds)
        src->cost (fn [src] (println src)  (-> src src->var var-info :STR))
        costs     (vec (for [v vars] (-> v var-info :STR)))]
    (->> (run 1 [q]
           ;; we want a map from SRCs to their quantities
           (== q src->var)
           (everyg #(fd/in % (fd/interval (-> % var-info :lower) (-> % var-info :upper))) vars)
           ;; the real work
           (productsumo vars costs amount))
         first)))

;;very dumb initial solution.
(defn initial-solution [target src-data & {:keys [init-choices]}]
  ;;random initial solution for now.
  (let [choices (or init-choices
                    (reduce-kv (fn [acc src {:keys [quantities]}]
                                 (assoc acc src (rand-nth (keys quantities)))) {} src-data))
        {:keys [score excess]} (total-fill-scores choices src-data)]
    {:choices choices
     :variables (vec (for [[src {:keys [quantities]}] src-data
                           :when (not= (count quantities) 1)]
                       src))
     :src-data       src-data
     :total-score    score
     :total-excess   excess
     :total-strength (total-strength src-data choices)
     :target target}))

(defn cost [sol]
  (+ (* -100000 (Math/abs (strength-deviation sol)))
     (* 1000 (sol :total-score))
     (* 0.1  (sol :total-excess))))

;;so we have an initial solution, a cost function, and now we can
;;do some solving...

(defn optimize-structure [init]
  (-> (da/simple-anneal (comp - cost) init
          :step-function (fn step [_ sol] (random-move sol))
          :decay (ann/geometric-decay 0.95)
          :equilibration 100)
      :best-solution))


(comment

  ;;(def init (initial-solution 300000 src-data ))
  ;; balancer.core> (def init (initial-solution 300000 src-data ))
  ;; #'balancer.core/init
  ;; balancer.core> (def res (optimize-structure init))
  ;; #'balancer.core/res
  ;; balancer.core> (cost res)
  ;; 171670.5836140001
  ;; balancer.core> (def res (optimize-structure init))
  ;; #'balancer.core/res
  ;; balancer.core> (cost res)
  ;; 168419.6012639999
  ;; balancer.core> (def res (optimize-structure init))
  ;; #'balancer.core/res
  ;; balancer.core> (cost res)
  ;; 172779.8828390001
  ;; balancer.core> (def init-packed (initial-solution 300000 src-data :init-choices (pack src-data 300000)))
  ;; #'balancer.core/init-packed
  ;; balancer.core> (def res (optimize-structure init-packed))
  ;; #'balancer.core/res
  ;; balancer.core> (cost res)
  ;; 172783.69851500003
  ;; balancer.core> (def res (optimize-structure init-packed))
  ;; #'balancer.core/res
  ;; balancer.core> (cost res)
  ;; 174032.08194400003
  ;; balancer.core> (def res (optimize-structure init-packed))
  ;; #'balancer.core/res
  ;; balancer.core> (cost res)
  ;; 173864.5783999999
)
