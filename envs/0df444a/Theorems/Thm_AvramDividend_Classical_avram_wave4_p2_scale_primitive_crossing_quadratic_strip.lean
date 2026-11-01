-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_crossing_quadratic_strip
-- name    : AvramDividend.Classical.avram_wave4_p2_scale_primitive_crossing_quadratic_strip
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:19:19.190007+00:00
-- url     : https://prove2.me/theorems/5becd970-55cd-4485-97ff-37098fb810d6
-- title:
--   Quadratic small-jump strip mass for the original q-scale primitive
-- statement:
--   For a genuine source q-scale W and a small backward jump length 0<r<=1, the compensated generator kernel of the integrated scale U on the crossing strip (0,r) has finite absolute x-integral bounded by r^2 W(1). This proves the correct small-jump quadratic moment at the non-Gaussian zero boundary without assuming a Gaussian slope bound or global second derivative of W. Direct input into the product-integrability/Fubini argument for the primitive U.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 4, primitive compensated generator approach. Derives from accepted source crossing bound e61c323a and generic strip integration 36b53f5a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p2_scale_primitive_crossing_quadratic_strip
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (r : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    IntegrableOn
      (fun x : ℝ => |r * W x - ∫ t in (0 : ℝ)..x, W t|)
      (Ioo (0 : ℝ) r) ∧
      (∫ x in Ioo (0 : ℝ) r,
        |r * W x - ∫ t in (0 : ℝ)..x, W t|) ≤ W 1 * r ^ 2 := by sorry
