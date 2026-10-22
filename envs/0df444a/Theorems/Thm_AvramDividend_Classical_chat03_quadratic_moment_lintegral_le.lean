-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_quadratic_moment_lintegral_le
-- name    : AvramDividend.Classical.chat03_quadratic_moment_lintegral_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T09:39:53.525605+00:00
-- url     : https://prove2.me/theorems/f76e5c75-845b-476e-9148-5a0c31b662be
-- title:
--   Quadratic real second-moment bound transfers to a nonnegative Lebesgue integral
-- statement:
--   If the integral of the square of any real-valued function is finite and at most C, then the nonnegative Lebesgue integral of ENNReal.ofReal of its square is bounded by ENNReal.ofReal C. This is the exact interface needed to use real-valued second-moment assumptions in quantitative ENNReal tail bounds.
-- source:
--   The pinned theorem MeasureTheory.ofReal_integral_eq_lintegral_ofReal and the pointwise nonnegativity of real squares.

import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.chat03_quadratic_moment_lintegral_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → ℝ) (C : ℝ)
    (hY2 : Integrable (fun ω => (Y ω) ^ 2) P ∧
      ∫ ω, (Y ω) ^ 2 ∂P ≤ C) :
    (∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂P) ≤ ENNReal.ofReal C := by sorry
