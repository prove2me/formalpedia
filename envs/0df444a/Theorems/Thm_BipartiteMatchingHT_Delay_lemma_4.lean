-- Prove2me | Theorems.Thm_BipartiteMatchingHT_Delay_lemma_4
-- name    : BipartiteMatchingHT.Delay.lemma_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T19:14:50.96781+00:00
-- url     : https://prove2.me/theorems/40d2da44-2592-49c7-88dc-b477de33a9ad
-- title:
--   Lemma 4 — critical subsets iff topological prefixes
-- statement:
--   For a heavy-traffic admissible matching and any nonempty server subset $A$, the ratio $(1-\rho)/\Delta_\rho(A;M)$ converges to a strictly positive real number as $\rho\uparrow1$ if and only if $A$ is the union of the first $r$ component server sets in some topological order, for some $1\le r\le K$. Both implications and existence of the positive limit are retained.
--
--   Differences from the source:
--   - encoding: classes and servers indexed from 1; binary matrix and arbitrary rewards → Fin n and Fin m indexed from 0; Boolean compatibility; omit rewards; reason: reindexing preserves all instances and rewards do not affect queue dynamics or delays
--   - encoding: independent Poisson arrivals and exponential services under FCFS-ALIS → a finite-mark Poisson event chain with null idle-server events and explicit ordered-list updates; reason: constant-rate uniformization gives the same countable-state queue; no finite queue cap or rate restriction is imposed
--   - encoding: the limiting family of operationally stable matchings → existence of a supported invariant probability vector for every real load sufficiently close to 1 from below; reason: stationarity is invariant under constant-rate uniformization; the limiting family is interpreted as eventual membership, without assuming any slack or delay theorem
--   - encoding: flows summed only on compatible edges and limiting maximum flows → flows are zero off compatible edges; residual support uses all saturated nominal feasible flows; reason: zero extension preserves the objective, and saturation is the equivalent feasibility test in Remark 3 and equation (6)
--   - encoding: numbered maximal connected residual components and their permutations → connected-component quotient and bijections from Fin K to that quotient; reason: enumerates the same components and each reversed topological order exactly once, without choosing an artificial labeling
--   - encoding: a real limit as rho increases to 1 → Tendsto along nhdsWithin 1 (Ioo 0 1); reason: states existence of convergence from the specified load interval and never chooses an arbitrary value for an absent limit
--   - reading: a server prefix and an integer k → a nonempty server subset and 1 <= k <= K; reason: the state prefixes have 1 <= ell <= m and the proof on p.43 explicitly uses k=1,...,K
-- source:
--   Afèche, Caldentey and Gupta, On the Optimal Design of a Bipartite Matching Queueing System, Operations Research (catalog 2021), https://doi.org/10.1287/opre.2020.2027; acquired artifact dated November 3, 2019; citation_basis published; Lemma 4, printed/PDF p. 17

import Definitions.Def_BipartiteMatchingHT_Delay_Aggregates

open scoped BigOperators ENNReal
open Filter Topology

namespace BipartiteMatchingHT.Delay

theorem lemma_4
    {n m : ℕ} (D : BipartiteMatchingHT.Delay.Model n m)
    (hD : BipartiteMatchingHT.Delay.Admissible D)
    (A : Finset (Fin m)) (hA : A.Nonempty) :
    (∃ L : ℝ, 0 < L ∧ Tendsto (fun ρ : ℝ => (1 - ρ) / D.slack ρ A)
      (nhdsWithin 1 (Set.Ioo 0 1)) (nhds L)) ↔
    ∃ σ ∈ BipartiteMatchingHT.Delay.orders D, ∃ r : ℕ,
      1 ≤ r ∧ r ≤ BipartiteMatchingHT.Delay.componentCount D ∧
        A = BipartiteMatchingHT.Delay.prefixServers D σ r := by sorry

end BipartiteMatchingHT.Delay
