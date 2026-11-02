-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_ubv_original_zero_endpoint_preruin_affine_terminal_floor
-- name    : AvramDividend.Classical.avram_wave8_ubv_original_zero_endpoint_preruin_affine_terminal_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:18:28.543533+00:00
-- url     : https://prove2.me/theorems/83fa4b1d-d03d-42f7-83de-be8356a454d4
-- title:
--   Original UBV zero-boundary affine stopped terminal floor before ruin
-- statement:
--   For the actual original spectrally negative Lévy source and its admissible capped dividend D, every source reserve before ruin lies in [0,C]. With only the corrected core's positive-half-line continuity, open-interior C² and derivative at least 1, the all-cap inclusive gradient secant theorem gives w(riskProcess_t)≥w(0)+riskProcess_t. This holds at reserve zero and C=0/∞ where the stated pre-ruin condition is meaningful, without assuming a derivative or smoothness at zero, bounded variation, or any stronger filtration. It is a quantitative boundary floor extending mere terminal nonnegativity.
-- source:
--   Proved genuine source riskProcess_nonnegative_strictly_before_ruin 03a69d71-1387-4410-83a2-1fe59054ebe6, all-time cap lemma, all-cap inclusive gradient secant 44b01929-5817-44ac-9439-6eb3c9879f2c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonnegative_strictly_before_ruin
import Theorems.Thm_AvramDividend_Classical_admissibleLe_riskProcess_le_cap_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave8_ubv_original_zero_endpoint_preruin_affine_terminal_floor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω) :
    w 0 + riskProcess X x D t ω ≤
      w (riskProcess X x D t ω) := by sorry
