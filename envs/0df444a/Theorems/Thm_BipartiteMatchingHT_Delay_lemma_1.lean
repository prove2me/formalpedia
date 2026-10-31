-- Prove2me | Theorems.Thm_BipartiteMatchingHT_Delay_lemma_1
-- name    : BipartiteMatchingHT.Delay.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T19:14:35.802986+00:00
-- url     : https://prove2.me/theorems/8aaa2801-ec64-4fbd-9b47-2f4a3dc3a416
-- title:
--   Lemma 1 — max-flow saturation
-- statement:
--   For a stable matching at any $0\le\rho<1$, there exists a maximum supported feasible flow $\widetilde f$ whose total transported mass is
--   $$\sum_{i,j}\widetilde f_{ij}=\rho\sum_i\widetilde\lambda_i.$$
--   The maximum is attained, not merely a supremum. The zero-arrival endpoint is included. The primitives have arbitrary positive real nominal and service rates with equal totals.
--
--   Differences from the source:
--   - encoding: classes and servers indexed from 1; binary matrix and arbitrary rewards → Fin n and Fin m indexed from 0; Boolean compatibility; omit rewards; reason: reindexing preserves all instances and rewards do not affect queue dynamics or delays
--   - encoding: independent Poisson arrivals and exponential services under FCFS-ALIS → a finite-mark Poisson event chain with null idle-server events and explicit ordered-list updates; reason: constant-rate uniformization gives the same countable-state queue; no finite queue cap or rate restriction is imposed
--   - encoding: flows summed only on compatible edges and limiting maximum flows → flows are zero off compatible edges; residual support uses all saturated nominal feasible flows; reason: zero extension preserves the objective, and saturation is the equivalent feasibility test in Remark 3 and equation (6)
--   - encoding: stability at rho in [0,1) → supported event-kernel stationarity, including rho=0; reason: the endpoint has zero arrival flow and is retained; no heavy-traffic admissibility is added
-- source:
--   Afèche, Caldentey and Gupta, On the Optimal Design of a Bipartite Matching Queueing System, Operations Research (catalog 2021), https://doi.org/10.1287/opre.2020.2027; acquired artifact dated November 3, 2019; citation_basis published; Lemma 1, printed/PDF p. 12

import Definitions.Def_BipartiteMatchingHT_Delay_Aggregates

open scoped BigOperators ENNReal
open Filter Topology

namespace BipartiteMatchingHT.Delay

theorem lemma_1
    {n m : ℕ} (D : BipartiteMatchingHT.Delay.Model n m)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hstable : BipartiteMatchingHT.Delay.Stable D ρ) :
    ∃ f : Fin n → Fin m → ℝ, (D.network ρ).IsMaxFlow f ∧
      BipartiteMatchingHT.Delay.Transportation.value f = ρ * ∑ i, D.nominal i := by sorry

end BipartiteMatchingHT.Delay
