-- Prove2me | Theorems.Thm_BipartiteMatchingHT_Delay_lemma_5
-- name    : BipartiteMatchingHT.Delay.lemma_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T19:14:31.452678+00:00
-- url     : https://prove2.me/theorems/f954f855-9cd3-43ec-88b9-f5557af0ddfe
-- title:
--   Lemma 5 — normalized topological-order masses
-- statement:
--   For a heavy-traffic admissible matching, let $\mathcal T(M)$ contain all reversed topological orders of its residual components. Put
--   $$Q_\sigma=\prod_{r=1}^K\left(\sum_{\ell=1}^r\mu_{\mathcal S_{\sigma(\ell)}}\right)^{-1}.$$
--   There is at least one order, all its weights are positive, and their total is positive. For every order,
--   $$\lim_{\rho\uparrow1}\sum_{s\in\sigma}\pi_\rho(P_m(s))=\frac{Q_\sigma}{\sum_{\tau\in\mathcal T(M)}Q_\tau}.$$
--   The denominator includes every topological order exactly once. The finite-load normalization omission in the source proof does not alter this limiting statement.
--
--   Differences from the source:
--   - encoding: classes and servers indexed from 1; binary matrix and arbitrary rewards → Fin n and Fin m indexed from 0; Boolean compatibility; omit rewards; reason: reindexing preserves all instances and rewards do not affect queue dynamics or delays
--   - encoding: independent Poisson arrivals and exponential services under FCFS-ALIS → a finite-mark Poisson event chain with null idle-server events and explicit ordered-list updates; reason: constant-rate uniformization gives the same countable-state queue; no finite queue cap or rate restriction is imposed
--   - encoding: the limiting family of operationally stable matchings → existence of a supported invariant probability vector for every real load sufficiently close to 1 from below; reason: stationarity is invariant under constant-rate uniformization; the limiting family is interpreted as eventual membership, without assuming any slack or delay theorem
--   - encoding: numbered maximal connected residual components and their permutations → connected-component quotient and bijections from Fin K to that quotient; reason: enumerates the same components and each reversed topological order exactly once, without choosing an artificial labeling
--   - encoding: the stationary probabilities of compressed states → sums over the fibers of the actual reachable queue-state equilibrium law; reason: retains in-service customer classes for operational dynamics, then forgets them only in the observation map; includes busy count zero
--   - encoding: a real limit as rho increases to 1 → Tendsto along nhdsWithin 1 (Ioo 0 1); reason: states existence of convergence from the specified load interval and never chooses an arbitrary value for an absent limit
--   - encoding: normalized positive order weights → nonempty order set and positive individual and total weights are explicit conclusions; reason: records definedness of the source probability ratio; no positivity hypothesis is added
--   - encoding: flows summed only on compatible edges and limiting maximum flows → flows are zero off compatible edges; residual support uses all saturated nominal feasible flows; reason: zero extension preserves the objective, and saturation is the equivalent feasibility test in Remark 3 and equation (6)
-- source:
--   Afèche, Caldentey and Gupta, On the Optimal Design of a Bipartite Matching Queueing System, Operations Research (catalog 2021), https://doi.org/10.1287/opre.2020.2027; acquired artifact dated November 3, 2019; citation_basis published; Lemma 5, printed/PDF p. 19

import Definitions.Def_BipartiteMatchingHT_Delay_Aggregates

open scoped BigOperators ENNReal
open Filter Topology

namespace BipartiteMatchingHT.Delay

theorem lemma_5
    {n m : ℕ} (D : BipartiteMatchingHT.Delay.Model n m)
    (hD : BipartiteMatchingHT.Delay.Admissible D) :
    (BipartiteMatchingHT.Delay.orders D).Nonempty ∧
    0 < BipartiteMatchingHT.Delay.totalQ D ∧
    ∀ σ ∈ BipartiteMatchingHT.Delay.orders D,
      0 < BipartiteMatchingHT.Delay.Q D σ ∧
      Tendsto (fun ρ : ℝ => BipartiteMatchingHT.Delay.orderMass D ρ σ)
        (nhdsWithin 1 (Set.Ioo 0 1))
        (nhds (BipartiteMatchingHT.Delay.Q D σ / BipartiteMatchingHT.Delay.totalQ D)) := by sorry

end BipartiteMatchingHT.Delay
