-- Prove2me | Theorems.Thm_BipartiteMatchingHT_Delay_lemma_8
-- name    : BipartiteMatchingHT.Delay.lemma_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T19:14:12.019887+00:00
-- url     : https://prove2.me/theorems/572ac628-a550-4a57-86d1-22c9184ddae4
-- title:
--   Lemma 8 — common internal-normalization limit
-- statement:
--   For a heavy-traffic admissible matching, there is a single finite real constant $\theta$ such that $\theta_\sigma(\rho)\to\theta$ as $\rho\uparrow1$ for every topological order $\sigma$. Here
--   $$\theta_\sigma(\rho)=\sum_{s\in\sigma}\prod_{\ell\in\{1,\ldots,m\}\setminus I_\sigma}\Delta_\rho(\{s_1,\ldots,s_\ell\};M)^{-1},$$
--   and $I_\sigma$ is exactly the set of cumulative whole-component server-block sizes. Every internal server permutation is included; empty products equal one. The constant is common across orders for the fixed matching, not across different queueing systems.
--
--   Differences from the source:
--   - encoding: classes and servers indexed from 1; binary matrix and arbitrary rewards → Fin n and Fin m indexed from 0; Boolean compatibility; omit rewards; reason: reindexing preserves all instances and rewards do not affect queue dynamics or delays
--   - encoding: independent Poisson arrivals and exponential services under FCFS-ALIS → a finite-mark Poisson event chain with null idle-server events and explicit ordered-list updates; reason: constant-rate uniformization gives the same countable-state queue; no finite queue cap or rate restriction is imposed
--   - encoding: the limiting family of operationally stable matchings → existence of a supported invariant probability vector for every real load sufficiently close to 1 from below; reason: stationarity is invariant under constant-rate uniformization; the limiting family is interpreted as eventual membership, without assuming any slack or delay theorem
--   - encoding: numbered maximal connected residual components and their permutations → connected-component quotient and bijections from Fin K to that quotient; reason: enumerates the same components and each reversed topological order exactly once, without choosing an artificial labeling
--   - encoding: a real limit as rho increases to 1 → Tendsto along nhdsWithin 1 (Ioo 0 1); reason: states existence of convergence from the specified load interval and never chooses an arbitrary value for an absent limit
--   - encoding: flows summed only on compatible edges and limiting maximum flows → flows are zero off compatible edges; residual support uses all saturated nominal feasible flows; reason: zero extension preserves the objective, and saturation is the equivalent feasibility test in Remark 3 and equation (6)
-- source:
--   Afèche, Caldentey and Gupta, On the Optimal Design of a Bipartite Matching Queueing System, Operations Research (catalog 2021), https://doi.org/10.1287/opre.2020.2027; acquired artifact dated November 3, 2019; citation_basis published; Lemma 8, printed/PDF p. 46

import Definitions.Def_BipartiteMatchingHT_Delay_Aggregates

open scoped BigOperators ENNReal
open Filter Topology

namespace BipartiteMatchingHT.Delay

theorem lemma_8
    {n m : ℕ} (D : BipartiteMatchingHT.Delay.Model n m)
    (hD : BipartiteMatchingHT.Delay.Admissible D) :
    ∃ θ : ℝ, ∀ σ ∈ BipartiteMatchingHT.Delay.orders D,
      Tendsto (BipartiteMatchingHT.Delay.theta D σ)
        (nhdsWithin 1 (Set.Ioo 0 1)) (nhds θ) := by sorry

end BipartiteMatchingHT.Delay
