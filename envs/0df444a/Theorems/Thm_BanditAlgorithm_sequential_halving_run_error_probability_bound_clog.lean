-- Prove2me | Theorems.Thm_BanditAlgorithm_sequential_halving_run_error_probability_bound_clog
-- name    : BanditAlgorithm.sequential_halving_run_error_probability_bound_clog
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-02T16:24:40.647657+00:00
-- url     : https://prove2.me/theorems/11d3a2db-36dd-4941-85bf-5d65789553dc
-- title:
--   Sequential Halving error bound with $L=\lceil\log_2 k\rceil$ phases
-- statement:
--   Let $L=\lceil\log_2 k\rceil$ be the number of phases used by Sequential Halving. Consider a $k$-armed $1$-subgaussian bandit with arm means indexed in nonincreasing order, and assume $n\ge kL$. Let $H_2$ satisfy $i/\Delta_i^2\le H_2$ for every suboptimal arm, with ranks numbered from $1$.
--
--   For any policy and recommendation rule, restrict to histories satisfying the full deterministic Sequential Halving run invariant: the active set is halved in each of the $L$ phases, each active arm receives the prescribed number of fresh samples, and each survivor has phase empirical mean at least that of every eliminated arm. Then
--
--   $$
--   \mathbb P(\text{valid run and suboptimal recommendation})
--   \le 3L\exp\!\left(-\frac{n}{16H_2L}\right).
--   $$
--
--   This is the direct general-$k$ phase-count form of the Sequential Halving analysis. It isolates the concentration argument from implementation and tie-breaking details.
--
--   **Formalization Note** Here $L$ is represented by `Nat.clog 2 k`, matching the number of phases in `IsSeqHalvingRun`.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Algorithm 22 and Exercise 33.8(c)–(f), printed pp. 412–413 and 419–420. The displayed L-bound is the direct general-k phase-count form of the exercise proof.

import Definitions.Def_SequentialHalving

open MeasureTheory

theorem BanditAlgorithm.sequential_halving_run_error_probability_bound_clog {k n : ℕ}
    (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    (hsorted : ∀ i j : Fin k, i ≤ j → banditArmMean ν j ≤ banditArmMean ν i)
    (hn : k * Nat.clog 2 k ≤ n) (H₂ : ℝ)
    (hH₂ : ∀ i : Fin k, 0 < banditGap ν i →
      ((i : ℕ) + 1 : ℝ) / banditGap ν i ^ 2 ≤ H₂)
    (π : BanditPolicy k) (rec : BanditHistory k n → Fin k) :
    (banditMeasure ν π n).real
        {h | IsSeqHalvingRun k n h (rec h) ∧ 0 < banditGap ν (rec h)} ≤
      3 * (Nat.clog 2 k : ℝ) *
        Real.exp (-(n / (16 * H₂ * (Nat.clog 2 k : ℝ)))) := by
  sorry
