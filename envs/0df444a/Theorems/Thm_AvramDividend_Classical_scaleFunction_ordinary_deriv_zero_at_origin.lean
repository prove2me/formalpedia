-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_ordinary_deriv_zero_at_origin
-- name    : AvramDividend.Classical.scaleFunction_ordinary_deriv_zero_at_origin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:32:11.989903+00:00
-- url     : https://prove2.me/theorems/b24ea912-8ee9-448e-a266-b7bad890c963
-- title:
--   Ordinary scale derivative is zero at a nonnegative zero boundary
-- statement:
--   For a canonical q-scale function that vanishes at the origin, its ordinary two-sided real derivative is zero. The scale-function axioms make it nonnegative on all reals, so the origin is a global minimum and the ordinary derivative vanishes by Fermat's theorem, including Mathlib's zero-at-nondifferentiable convention. This exposes the necessary distinction between ordinary derivative at zero and right-hand Gaussian slope 2/sigma squared.
-- source:
--   Elementary Fermat calculus; scale-function defining axioms.

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- The ordinary two-sided derivative at a zero boundary minimum is zero. -/
theorem scaleFunction_ordinary_deriv_zero_at_origin
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0) :
    deriv W 0 = 0 := by
  sorry

end AvramDividend.Classical
