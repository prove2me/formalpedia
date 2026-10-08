-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_derivZeroPlus_nonneg
-- name    : AvramDividend.Classical.scaleFunction_derivZeroPlus_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T18:01:57.211947+00:00
-- url     : https://prove2.me/theorems/d5cff500-3627-42d6-88e0-9053374e1bb7
-- title:
--   Nonnegative extended right derivative of a canonical q-scale function
-- statement:
--   For every function satisfying the canonical Avram IsScaleFunction hypothesis, the right-hand extended derivative liminf at zero is nonnegative. This rules out the EReal negative-infinity case at the zero dividend barrier, and follows directly from the already Proved nonnegative ordinary derivative at all positive points together with the general right-liminf lower-bound bridge.
-- source:
--   Apply deriv_global_lower_le_right_liminf W with d=0 to the globally nonnegative ordinary scale derivative guaranteed by the Proved scaleDeriv_nonneg. The result transfers process-level monotonicity to the right-boundary EReal derivative convention.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_derivZeroPlus_nonneg
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    (0 : EReal) ≤ derivZeroPlus W := by
  sorry

end AvramDividend.Classical
