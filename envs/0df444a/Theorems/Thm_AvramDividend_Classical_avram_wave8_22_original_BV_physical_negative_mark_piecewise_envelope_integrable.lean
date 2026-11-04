-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_physical_negative_mark_piecewise_envelope_integrable
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_physical_negative_mark_piecewise_envelope_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:26:54.842741+00:00
-- url     : https://prove2.me/theorems/9d4c3c9b-8c04-4ca1-9610-bb38c49395f6
-- title:
--   Original BV negative Lévy mark near-linear far-constant envelope is integrable
-- statement:
--   For the genuine bounded-variation spectrally negative Lévy measure, the piecewise negative-mark function which is L times the absolute jump on the small band and the constant 2R on the separated large-jump band is integrable over all negative marks. The source BV first moment controls near-zero activity and the genuine Lévy energy yields finite mass away from zero.
-- source:
--   Accepted physical BV small negative first moment and the accepted exact original negative Lévy tail finite mass 0c671eeb. Extracted integrability core of original W8-22 uniform physical ν integral estimate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_small_negative_first_moment_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_negative_levy_tail_finite_at_BV_C1_threshold
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_physical_negative_mark_piecewise_envelope_integrable
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (a L R : ℝ) (ha : 0 < a) (ha2 : a ≤ 2)
  (hL : 0 ≤ L) (hR : 0 ≤ R) :
  IntegrableOn (fun z : ℝ => if z ≤ -a / 2 then 2 * R else L * (-z))
    (Iio (0 : ℝ)) X.ν := by sorry
