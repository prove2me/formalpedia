-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_lintegral_bound_implies_real_integral_bound
-- name    : AvramDividend.Classical.chat03_lintegral_bound_implies_real_integral_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:04:31.745188+00:00
-- url     : https://prove2.me/theorems/1c368e9b-9b46-4b64-af82-664ab3f67e2d
-- title:
--   Transfer of a finite nonnegative integral bound to a real expectation
-- statement:
--   An extended nonnegative integral upper bound for an almost-everywhere nonnegative integrable real function transfers to the usual Bochner expectation, provided the real upper bound is nonnegative. This avoids treating ENNReal.toReal as continuous at infinity.
-- source:
--   MeasureTheory.ofReal_integral_eq_lintegral_ofReal and ENNReal.ofReal_le_ofReal_iff.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.ENNReal.Real

open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.chat03_lintegral_bound_implies_real_integral_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℝ) (C : ℝ)
    (hfi : Integrable f P) (hf0 : ∀ᵐ ω ∂P, 0 ≤ f ω)
    (hC : 0 ≤ C)
    (hbound : (∫⁻ ω, ENNReal.ofReal (f ω) ∂P) ≤ ENNReal.ofReal C) :
    (∫ ω, f ω ∂P) ≤ C := by sorry
