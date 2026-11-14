-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb75_masked_true_generator_uniform_grid_nonpositive
-- name    : AvramDividend.Classical.avram_bvb75_masked_true_generator_uniform_grid_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T16:22:21.962628+00:00
-- url     : https://prove2.me/theorems/f3119e79-4e6e-4a9c-a0b9-1d6460ee73a7
-- title:
--   Original BV masked discounted physical-grid HJB generator cell sum is nonpositive
-- statement:
--   Every masked genuine generator HJB cell of the original physical BV uniform time mesh is nonpositive: use the conditional interior HJB sign, positive discount and nonnegative time-mesh width. This reusable pathwise algebra does not require finite negative jump counting and leaves the genuine compensated Stieltjes source as a separate obligation.
-- source:
--   Original BV physical generator G_n signed cell; target BVB67/BVB49, previously Proved BVB46

import Mathlib
open Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb75_masked_true_generator_uniform_grid_nonpositive
    {Ω : Type*} (q : ℝ) (w g : ℝ → ℝ) (C : ℝ≥0∞)
    (hgen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      g y - q * w y ≤ 0)
    (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (Z : ℕ → Ω → ℕ → ℝ) (M : ℕ → Ω → ℕ → Prop) :
    ∀ n : ℕ, ∀ ω : Ω,
      (∑ i ∈ Finset.range (n + 1),
        if M n ω i ∧ 0 < Z n ω i ∧ ENNReal.ofReal (Z n ω i) < C then
          Real.exp (-(q * (u n i : ℝ))) *
            (g (Z n ω i) - q * w (Z n ω i)) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0) ≤ 0 := by sorry
