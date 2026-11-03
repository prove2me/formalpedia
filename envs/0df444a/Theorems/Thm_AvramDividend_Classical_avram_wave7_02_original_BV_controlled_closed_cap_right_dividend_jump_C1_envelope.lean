-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_controlled_closed_cap_right_dividend_jump_C1_envelope
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_controlled_closed_cap_right_dividend_jump_C1_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:11:42.185463+00:00
-- url     : https://prove2.me/theorems/5b4795bc-0ce3-494c-b90a-d6c7c151602b
-- title:
--   Original controlled BV right-dividend jump obeys the HJB candidate-value drop even at cap equality
-- statement:
--   For the original standing spectrally negative Levy process with admissible dividend control, a nonnegative right-payment increment that does not overdraw the reserve satisfies the canonical hjump inequality whenever the pre-payment reserve is at or below positive cap C, including equality. The derivative≥1 HJB assumption on the strict interior plus continuity at the cap suffice; exact riskProcess and rightLimit D are preserved.
-- source:
--   Source-faithful controlled reserve application of the closed-cap two-point C1 gradient theorem, including the original rightLimit D jump and no alternative random process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_closed_endpoint_two_point_jump_envelope
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_controlled_closed_cap_right_dividend_jump_C1_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0),
      0 ≤ riskProcess X x D t ω -
        (rightLimit D t ω - D t ω) →
      0 ≤ rightLimit D t ω - D t ω →
      ENNReal.ofReal (riskProcess X x D t ω) ≤ C →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)) := by sorry
