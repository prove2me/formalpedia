-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_discounted_masked_compact_Hessian_uniform_upper
-- name    : AvramDividend.Classical.avram_ga_discounted_masked_compact_Hessian_uniform_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T17:47:36.614439+00:00
-- url     : https://prove2.me/theorems/b4429e67-85e2-433e-b2ee-cf3f71a1392e
-- title:
--   Uniform discounted clipped Hessian bound along lower-controlled stopped grid mask
-- statement:
--   Whenever the stopped physical-grid sample values Y have a lower bound a on active cells, the clipped Hessian coefficient exp(-q s)*(if Y<=b then w double derivative else zero) has a deterministic uniform absolute bound, provided w second derivative is continuous on [a,b] and discount q is nonnegative. The inactive and upper strip are handled by the zero coefficient, not by requiring the reserve below b globally.

import Mathlib
open Set Filter Topology MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.avram_ga_discounted_masked_compact_Hessian_uniform_upper
    {Ω : Type*} (w : ℝ → ℝ) (a b q : ℝ) (hq : 0 ≤ q)
    (hCont : ContinuousOn (fun y => iteratedDeriv 2 w y) (Icc a b))
    (Y : ℕ → ℕ → Ω → ℝ) (s : ℕ → ℕ → ℝ≥0)
    (mask : ℕ → ℕ → Ω → Prop)
    (hFloor : ∀ m i ω, mask m i ω → a ≤ Y m i ω) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m i ω, mask m i ω →
      |Real.exp (-(q * (s m i : ℝ))) *
        (if Y m i ω ≤ b then iteratedDeriv 2 w (Y m i ω) else 0)| ≤ K := by sorry
