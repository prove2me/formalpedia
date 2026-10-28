-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_finite_minimum_pointwise_mono
-- name    : AvramDividend.Classical.chat08_finite_minimum_pointwise_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:25:23.437175+00:00
-- url     : https://prove2.me/theorems/8086a917-a0a2-4f8e-a862-a1f3fe767dd7
-- title:
--   Monotonicity of finite first-passage clocks under pointwise observation comparisons
-- statement:
--   Every observation time no later than the corresponding other clock yields a finite running-minimum clock no later than the other finite running-minimum clock, pathwise for each prefix.
-- source:
--   Natural-number induction and monotonicity of the minimum operation.

import Mathlib.Probability.Process.Stopping

open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat08_finite_minimum_pointwise_mono
    {Ω : Type*} (τ υ : ℕ → Ω → WithTop ℝ≥0)
    (hτυ : ∀ k ω, τ k ω ≤ υ k ω) :
    ∀ n ω, (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
      (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun j σ ω => min (τ j ω) (σ ω)) n) ω ≤
      (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
      (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun j σ ω => min (υ j ω) (σ ω)) n) ω := by sorry
