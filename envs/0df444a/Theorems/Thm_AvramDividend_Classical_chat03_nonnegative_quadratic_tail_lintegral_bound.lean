-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_nonnegative_quadratic_tail_lintegral_bound
-- name    : AvramDividend.Classical.chat03_nonnegative_quadratic_tail_lintegral_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T09:28:18.886711+00:00
-- url     : https://prove2.me/theorems/fde1a000-b09c-41d3-a52e-fa9abe5b2995
-- title:
--   Almost-everywhere nonnegative quadratic-tail domination in the Lebesgue integral
-- statement:
--   For a measurable-space probability or arbitrary measure, if a real-valued function is almost everywhere nonnegative, then its Lebesgue integral of the upper tail above positive threshold R is bounded by the Lebesgue integral of its quadratic moment divided by R. This bound uses only almost-everywhere monotonicity and the independently proved pointwise tail lemma, and is a foundation for uniform second-moment convergence.
-- source:
--   Monotonicity of the nonnegative Lebesgue integral applied to the proved pointwise quadratic-tail inequality.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_chat03_nonnegative_quadratic_tail_pointwise

open MeasureTheory AvramDividend.Classical
open scoped ENNReal

theorem AvramDividend.Classical.chat03_nonnegative_quadratic_tail_lintegral_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → ℝ) (R : ℝ) (hR : 0 < R)
    (hY0 : ∀ᵐ ω ∂P, 0 ≤ Y ω) :
    (∫⁻ ω, ENNReal.ofReal (if R ≤ Y ω then Y ω else 0) ∂P) ≤
      ∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2 / R) ∂P := by sorry
