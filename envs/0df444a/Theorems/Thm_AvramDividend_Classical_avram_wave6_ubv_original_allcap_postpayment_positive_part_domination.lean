-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_ubv_original_allcap_postpayment_positive_part_domination
-- name    : AvramDividend.Classical.avram_wave6_ubv_original_allcap_postpayment_positive_part_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:38:53.566969+00:00
-- url     : https://prove2.me/theorems/9ae5dedd-b82e-4205-9f96-af361b8e4e08
-- title:
--   Original all-cap post-payment terminal candidate dominates reserve positive part
-- statement:
--   For actual original source SpectrallyNegativeLevy P 𝓕 and admissible D, the corrected value candidate at the reserve after the strategy right jump dominates the positive part of that post-payment reserve for every sample path and time, all caps including C=0, with 0≤w(0). Positive reserve uses the already Proved inclusive gradient secant and source post-payment cap, zero creeping uses w(0)≥0, and negative overshoot uses w(y)=0. No endpoint C², bounded variation, filtration change, or atomlessness assumption.
-- source:
--   Accepted all-cap postpayment terminal nonnegativity 06839544-2429-48b2-bce8-78e4b76dd814, source postpayment cap 16104f4f-861a-44e4-8c74-94a125730fa3, inclusive gradient secant 44b01929-5817-44ac-9439-6eb3c9879f2c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_allcap_postpayment_terminal_candidate_nonnegative

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_ubv_original_allcap_postpayment_positive_part_domination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0),
      max 0 (x + X.X t ω - rightLimit D t ω) ≤
        w (x + X.X t ω - rightLimit D t ω) := by sorry
