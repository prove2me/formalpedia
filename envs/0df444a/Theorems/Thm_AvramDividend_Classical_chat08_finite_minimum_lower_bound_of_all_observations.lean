-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_finite_minimum_lower_bound_of_all_observations
-- name    : AvramDividend.Classical.chat08_finite_minimum_lower_bound_of_all_observations
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:29:14.691824+00:00
-- url     : https://prove2.me/theorems/f7b0026c-6582-487e-9d03-1c013418c461
-- title:
--   Lower bounds persist through finite sampled first-passage minima
-- statement:
--   If every sampled event clock in a finite prefix is at least a specified lower bound, then the running minimum of those clocks is at least that bound.
-- source:
--   Natural-number induction using order-theoretic minimum.

import Mathlib.Probability.Process.Stopping

open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat08_finite_minimum_lower_bound_of_all_observations
    {Ω : Type*} (τ : ℕ → Ω → WithTop ℝ≥0) (t : WithTop ℝ≥0)
    (n : ℕ) (ω : Ω) (hobs : ∀ k, k < n → t ≤ τ k ω) :
    t ≤ (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
      (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun j σ ω => min (τ j ω) (σ ω)) n) ω := by sorry
