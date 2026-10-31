-- Prove2me | Theorems.Thm_BipartiteMatchingHT_Delay_lemma_6
-- name    : BipartiteMatchingHT.Delay.lemma_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T19:14:20.423238+00:00
-- url     : https://prove2.me/theorems/ff4802cc-9e20-4ab6-baaf-0c43465e07d0
-- title:
--   Lemma 6 — finite-load stationary waiting-time identity
-- statement:
--   For a heavy-traffic admissible matching and every $0<\rho<1$, the operational stationary class-$i$ waiting time has a finite mean. Every nonempty server subset has positive slack, and
--   $$W_i(\rho)=\sum_{s\in\Sigma_m}\sum_{b=1}^m\left(\sum_{\ell=1}^b\frac{\mathbf 1\{i\in U(s_1,\ldots,s_\ell;M)\}}{\Delta_\rho(\{s_1,\ldots,s_\ell\};M)}\right)\pi_\rho(P_b(s)).$$
--   This is an exact finite-load identity for expected queueing delay until service starts. The left side is defined by a tagged-arrival experiment, independently of this rational expression.
--
--   Differences from the source:
--   - encoding: classes and servers indexed from 1; binary matrix and arbitrary rewards → Fin n and Fin m indexed from 0; Boolean compatibility; omit rewards; reason: reindexing preserves all instances and rewards do not affect queue dynamics or delays
--   - encoding: independent Poisson arrivals and exponential services under FCFS-ALIS → a finite-mark Poisson event chain with null idle-server events and explicit ordered-list updates; reason: constant-rate uniformization gives the same countable-state queue; no finite queue cap or rate restriction is imposed
--   - encoding: the limiting family of operationally stable matchings → existence of a supported invariant probability vector for every real load sufficiently close to 1 from below; reason: stationarity is invariant under constant-rate uniformization; the limiting family is interpreted as eventual membership, without assuming any slack or delay theorem
--   - encoding: the stationary probabilities of compressed states → sums over the fibers of the actual reachable queue-state equilibrium law; reason: retains in-service customer classes for operational dynamics, then forgets them only in the observation map; includes busy count zero
--   - encoding: stationary mean waiting until service starts → an extended nonnegative tagged-arrival hitting-time tail sum, with finite mean concluded before real conversion; reason: the independent exponential event intervals have mean 1/R, giving the same waiting expectation, including an infinite value when needed
--   - encoding: finite stationary mean and reciprocal slacks → finite mean, finite-load stability, and positive nonempty-subset slacks are explicit conclusions; reason: protects real conversion and division using the source stable regime, without assuming the waiting-time identity
-- source:
--   Afèche, Caldentey and Gupta, On the Optimal Design of a Bipartite Matching Queueing System, Operations Research (catalog 2021), https://doi.org/10.1287/opre.2020.2027; acquired artifact dated November 3, 2019; citation_basis published; Lemma 6, printed/PDF p. 19

import Definitions.Def_BipartiteMatchingHT_Delay_Aggregates

open scoped BigOperators ENNReal
open Filter Topology

namespace BipartiteMatchingHT.Delay

theorem lemma_6
    {n m : ℕ} (D : BipartiteMatchingHT.Delay.Model n m)
    (hD : BipartiteMatchingHT.Delay.Admissible D)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) (i : Fin n) :
    BipartiteMatchingHT.Delay.Stable D ρ ∧
    BipartiteMatchingHT.Delay.meanWait D ρ i < ⊤ ∧
    (∀ A : Finset (Fin m), A.Nonempty → 0 < D.slack ρ A) ∧
    (BipartiteMatchingHT.Delay.meanWait D ρ i).toReal =
      BipartiteMatchingHT.Delay.finiteWaitFormula D ρ i := by sorry

end BipartiteMatchingHT.Delay
