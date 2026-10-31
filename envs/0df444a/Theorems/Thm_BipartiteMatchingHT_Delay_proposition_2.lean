-- Prove2me | Theorems.Thm_BipartiteMatchingHT_Delay_proposition_2
-- name    : BipartiteMatchingHT.Delay.proposition_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T19:14:40.019871+00:00
-- url     : https://prove2.me/theorems/771930fc-b628-4599-bc3d-6472f2ef6f54
-- title:
--   Proposition 2 — vanishing aggregate-state probabilities
-- statement:
--   For a heavy-traffic admissible matching, a server permutation $s$, and a busy count $0\le b\le m$, suppose either $b<m$ or $s$ is not induced by any topological order. Then
--   $$\lim_{\rho\uparrow1}\pi_\rho(P_b(s))=0.$$
--   The disjunction includes fully busy non-induced permutations and the all-idle case. The probability is obtained from the operational stationary queue, not from a proposed asymptotic distribution.
--
--   Differences from the source:
--   - encoding: classes and servers indexed from 1; binary matrix and arbitrary rewards → Fin n and Fin m indexed from 0; Boolean compatibility; omit rewards; reason: reindexing preserves all instances and rewards do not affect queue dynamics or delays
--   - encoding: independent Poisson arrivals and exponential services under FCFS-ALIS → a finite-mark Poisson event chain with null idle-server events and explicit ordered-list updates; reason: constant-rate uniformization gives the same countable-state queue; no finite queue cap or rate restriction is imposed
--   - encoding: the limiting family of operationally stable matchings → existence of a supported invariant probability vector for every real load sufficiently close to 1 from below; reason: stationarity is invariant under constant-rate uniformization; the limiting family is interpreted as eventual membership, without assuming any slack or delay theorem
--   - encoding: numbered maximal connected residual components and their permutations → connected-component quotient and bijections from Fin K to that quotient; reason: enumerates the same components and each reversed topological order exactly once, without choosing an artificial labeling
--   - encoding: the stationary probabilities of compressed states → sums over the fibers of the actual reachable queue-state equilibrium law; reason: retains in-service customer classes for operational dynamics, then forgets them only in the observation map; includes busy count zero
--   - encoding: a real limit as rho increases to 1 → Tendsto along nhdsWithin 1 (Ioo 0 1); reason: states existence of convergence from the specified load interval and never chooses an arbitrary value for an absent limit
-- source:
--   Afèche, Caldentey and Gupta, On the Optimal Design of a Bipartite Matching Queueing System, Operations Research (catalog 2021), https://doi.org/10.1287/opre.2020.2027; acquired artifact dated November 3, 2019; citation_basis published; Proposition 2, printed/PDF p. 18

import Definitions.Def_BipartiteMatchingHT_Delay_Aggregates

open scoped BigOperators ENNReal
open Filter Topology

namespace BipartiteMatchingHT.Delay

theorem proposition_2
    {n m : ℕ} (D : BipartiteMatchingHT.Delay.Model n m)
    (hD : BipartiteMatchingHT.Delay.Admissible D)
    (s : Equiv.Perm (Fin m)) (b : ℕ) (hb : b ≤ m)
    (hvanish : b < m ∨ ¬ ∃ σ ∈ BipartiteMatchingHT.Delay.orders D,
      BipartiteMatchingHT.Delay.Induced D σ s) :
    Tendsto (fun ρ : ℝ => BipartiteMatchingHT.Delay.aggregateMass D ρ s b)
      (nhdsWithin 1 (Set.Ioo 0 1)) (nhds 0) := by sorry

end BipartiteMatchingHT.Delay
