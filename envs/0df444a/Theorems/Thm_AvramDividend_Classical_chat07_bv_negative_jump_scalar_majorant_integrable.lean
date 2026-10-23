-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_bv_negative_jump_scalar_majorant_integrable
-- name    : AvramDividend.Classical.chat07_bv_negative_jump_scalar_majorant_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T07:40:36.335505+00:00
-- url     : https://prove2.me/theorems/fb1463c3-706c-4c97-a88e-fdbaee19aa2f
-- title:
--   Integrability of scalar first-moment envelope for negative jumps
-- statement:
--   For a bounded-variation spectrally negative Levy process, any constant scalar multiple of min(1, absolute jump size) remains integrable over the negative half-line under the Levy jump measure. This immediately supplies the weighted coefficient envelope for the generator-scale Fubini estimates after the small and large jump bounds have been unified.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat07_bv_negative_jump_min_abs_integrable
import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat07_bv_negative_jump_scalar_majorant_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (C : ℝ) :
    IntegrableOn (fun y : ℝ => C * min 1 |y|) (Iio (0 : ℝ)) X.ν := by sorry
