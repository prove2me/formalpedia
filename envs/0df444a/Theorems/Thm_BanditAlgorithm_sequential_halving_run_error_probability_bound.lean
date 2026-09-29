-- Prove2me | Theorems.Thm_BanditAlgorithm_sequential_halving_run_error_probability_bound
-- name    : BanditAlgorithm.sequential_halving_run_error_probability_bound
-- status  : Open
-- author  : @Harry_Xu
-- created : 2026-07-30T19:43:02.905649+00:00
-- url     : https://prove2.me/theorems/3f9c352c-0549-43b3-9d53-615d09f9d90f
-- title:
--   Sequential Halving error bound on valid runs
-- statement:
--   Consider a $k$-armed $1$-subgaussian bandit whose means are indexed in nonincreasing order, and a budget $n$ large enough that every phase of Sequential Halving samples every active arm at least once. Let $H_2$ be any common upper bound satisfying
--
--   $$
--   \frac{i}{\Delta_i^2}\le H_2
--   $$
--
--   for each suboptimal arm, with arm indices numbered from $1$. For an arbitrary policy and recommendation rule, restrict attention to the histories that satisfy the complete deterministic Sequential Halving run invariant: the active sets halve with the prescribed cardinalities, every active arm receives the prescribed number of fresh phase samples, and survivors have empirical means at least those of eliminated arms. Then the probability of such a valid run ending with a suboptimal recommendation is at most
--
--   $$
--   3\log_2(k)\exp\!\left(-\frac{n}{16H_2\log_2(k)}\right).
--   $$
--
--   This is the concentration core of the fixed-budget Sequential Halving guarantee. Separating it from the policy-level theorem makes the result reusable for any implementation or tie-breaking rule whose realized histories satisfy the same run invariant.
--
--   **Formalization Note** The event explicitly includes `IsSeqHalvingRun`; no assumption is made here that the supplied policy produces valid runs almost surely.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Theorem 33.10, printed p. 412, with the detailed phase-elimination argument in Exercise 33.8(c)--(f), printed pp. 419--420.

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_SequentialHalving

open MeasureTheory

theorem BanditAlgorithm.sequential_halving_run_error_probability_bound {k n : ℕ}
    (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    (hsorted : ∀ i j : Fin k, i ≤ j → banditArmMean ν j ≤ banditArmMean ν i)
    (hn : k * Nat.clog 2 k ≤ n) (H₂ : ℝ)
    (hH₂ : ∀ i : Fin k, 0 < banditGap ν i →
      ((i : ℕ) + 1 : ℝ) / banditGap ν i ^ 2 ≤ H₂)
    (π : BanditPolicy k) (rec : BanditHistory k n → Fin k) :
    (banditMeasure ν π n).real
        {h | IsSeqHalvingRun k n h (rec h) ∧ 0 < banditGap ν (rec h)} ≤
      3 * Real.logb 2 k * Real.exp (-(n / (16 * H₂ * Real.logb 2 k))) := by
  sorry
