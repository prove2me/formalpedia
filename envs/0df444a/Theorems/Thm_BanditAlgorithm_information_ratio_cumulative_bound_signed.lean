-- Prove2me | Theorems.Thm_BanditAlgorithm_information_ratio_cumulative_bound_signed
-- name    : BanditAlgorithm.information_ratio_cumulative_bound_signed
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T21:18:21.404433+00:00
-- url     : https://prove2.me/theorems/cfdd988e-c7c2-45e1-a620-2be3c0904489
-- title:
--   Signed finite-horizon information-ratio bound
-- statement:
--   Let $n$ be a finite horizon. For every round $t$, let $\delta_t$ be a (possibly signed) instantaneous regret and let $I_t$ be an information term. Suppose $\Gamma,H\ge 0$, the pointwise information-ratio inequalities
--
--   $$
--   \delta_t^2\le \Gamma I_t
--   $$
--
--   hold for all $t$, and the total information satisfies $\sum_{t=1}^n I_t\le H$. Then
--
--   $$
--   \sum_{t=1}^n \delta_t\le \sqrt{n\Gamma H}.
--   $$
--
--   This signed form is the precise finite-sum Cauchy--Schwarz step needed for Bayesian adversarial bandits, where a round's conditional expected regret need not be separately nonnegative.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), Theorem 36.6, printed pp. 470-471, especially the Cauchy-Schwarz calculation in Eq. (36.10).

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators

theorem BanditAlgorithm.information_ratio_cumulative_bound_signed {n : ℕ}
    (δ info : Fin n → ℝ) (Γ H : ℝ)
    (hΓ : 0 ≤ Γ) (hH : 0 ≤ H)
    (hpoint : ∀ t, δ t ^ 2 ≤ Γ * info t)
    (hsum : ∑ t, info t ≤ H) :
    ∑ t, δ t ≤ Real.sqrt (n * Γ * H) := by
  sorry
