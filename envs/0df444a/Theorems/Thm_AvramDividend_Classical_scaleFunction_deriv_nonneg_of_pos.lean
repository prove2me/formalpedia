-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_deriv_nonneg_of_pos
-- name    : AvramDividend.Classical.scaleFunction_deriv_nonneg_of_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:50:45.177999+00:00
-- url     : https://prove2.me/theorems/6b1eb6d0-7bad-4d18-87e0-1821373a0129
-- title:
--   The ordinary derivative of a monotone q-scale function is nonnegative at positive arguments
-- statement:
--   The canonical q-scale function is nondecreasing on [0,infinity). At a positive argument it agrees locally with the globally monotone real function z↦W(max(z,0)). The derivative of a monotone real function is nonnegative under Lean's derivative convention, even without differentiability (where deriv defaults to zero). This yields nonnegativity of the ordinary derivative at each strictly positive argument. This result is the reusable pathwise real-analysis component of the already accepted zero-barrier nonnegativity proof and is useful for denominator signs in early barrier and initial-excess dividend value calculations.
-- source:
--   Canonical IsScaleFunction monotonicity axiom and Mathlib Monotone.deriv_nonneg, Filter.EventuallyEq.deriv_eq.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical
theorem scaleFunction_deriv_nonneg_of_pos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) :
    0 ≤ deriv W a := by sorry
end AvramDividend.Classical
