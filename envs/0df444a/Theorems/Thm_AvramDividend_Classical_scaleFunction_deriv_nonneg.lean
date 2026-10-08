-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_deriv_nonneg
-- name    : AvramDividend.Classical.scaleFunction_deriv_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T15:31:34.632175+00:00
-- url     : https://prove2.me/theorems/329e96a9-e531-4cb6-a7b5-b69b51eec323
-- title:
--   Nonnegative ordinary derivative of the canonical q-scale function at every positive point
-- statement:
--   Every q-scale function satisfying the canonical Avram IsScaleFunction definition has a nonnegative real derivative at every strictly positive x. This follows directly from the definition's monotonicity on the nonnegative half-line. It remains valid where differentiability fails because Mathlib's ordinary derivative convention is zero there. This proves a basic genuine consequence of the original scale-function assumptions, rather than adding a further differentiability premise.
-- source:
--   Pinned Mathlib Analysis.Calculus.Deriv.Slope provides MonotoneOn.derivWithin_nonneg. At any x>0, the closed half-line Ici 0 is a neighbourhood of x, so the pinned derivWithin_of_mem_nhds theorem identifies its within-derivative with the ordinary derivative. IsScaleFunction gives the MonotoneOn property as conjunction projection hW.2.2.2.1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_deriv_nonneg
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 < x) :
    0 ≤ deriv W x := by
  sorry

end AvramDividend.Classical
