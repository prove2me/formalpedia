-- Prove2me | Theorems.Thm_BipartiteMatchingHT_Delay_lemma_2
-- name    : BipartiteMatchingHT.Delay.lemma_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T19:14:24.242206+00:00
-- url     : https://prove2.me/theorems/cf3cfffb-6baf-4c3d-bd15-4a6980385eeb
-- title:
--   Lemma 2 — acyclicity of the component graph
-- statement:
--   For every heavy-traffic admissible matching, the directed graph on its residual connected components is acyclic. Arcs are exactly original compatible edges missing from the union of positive supports of saturated nominal flows. There is no positive-length directed path from any component back to itself, including a one-edge self loop.
--
--   Differences from the source:
--   - encoding: classes and servers indexed from 1; binary matrix and arbitrary rewards → Fin n and Fin m indexed from 0; Boolean compatibility; omit rewards; reason: reindexing preserves all instances and rewards do not affect queue dynamics or delays
--   - encoding: independent Poisson arrivals and exponential services under FCFS-ALIS → a finite-mark Poisson event chain with null idle-server events and explicit ordered-list updates; reason: constant-rate uniformization gives the same countable-state queue; no finite queue cap or rate restriction is imposed
--   - encoding: the limiting family of operationally stable matchings → existence of a supported invariant probability vector for every real load sufficiently close to 1 from below; reason: stationarity is invariant under constant-rate uniformization; the limiting family is interpreted as eventual membership, without assuming any slack or delay theorem
--   - encoding: flows summed only on compatible edges and limiting maximum flows → flows are zero off compatible edges; residual support uses all saturated nominal feasible flows; reason: zero extension preserves the objective, and saturation is the equivalent feasibility test in Remark 3 and equation (6)
--   - encoding: numbered maximal connected residual components and their permutations → connected-component quotient and bijections from Fin K to that quotient; reason: enumerates the same components and each reversed topological order exactly once, without choosing an artificial labeling
--   - encoding: acyclic directed graph → no positive-length path from a component to itself; reason: transitive closure excludes all directed cycles including self loops
-- source:
--   Afèche, Caldentey and Gupta, On the Optimal Design of a Bipartite Matching Queueing System, Operations Research (catalog 2021), https://doi.org/10.1287/opre.2020.2027; acquired artifact dated November 3, 2019; citation_basis published; Lemma 2, printed/PDF p. 14

import Definitions.Def_BipartiteMatchingHT_Delay_Aggregates

open scoped BigOperators ENNReal
open Filter Topology

namespace BipartiteMatchingHT.Delay

theorem lemma_2
    {n m : ℕ} (D : BipartiteMatchingHT.Delay.Model n m)
    (hD : BipartiteMatchingHT.Delay.Admissible D) :
    ∀ k, ¬ Relation.TransGen (BipartiteMatchingHT.Delay.componentArc D) k k := by sorry

end BipartiteMatchingHT.Delay
