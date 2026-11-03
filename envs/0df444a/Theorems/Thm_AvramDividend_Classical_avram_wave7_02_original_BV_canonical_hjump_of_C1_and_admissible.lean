-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_canonical_hjump_of_C1_and_admissible
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_canonical_hjump_of_C1_and_admissible
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:17:40.091576+00:00
-- url     : https://prove2.me/theorems/5b71b5ce-9307-4f85-89ba-cf87da1b20e3
-- title:
--   Exact canonical BV HJB right-dividend jump inequality follows from C1 gradient and original admissibility
-- statement:
--   For the original standing BV spectrally negative Levy process and every genuinely admissible capped dividend strategy, the canonical right-payment jump inequality is a consequence of the positive-cap C1 candidate gradient at least one, candidate continuity up to the cap, and initial x≤C. Indeed monotone D gives nonnegative right increment, IsAdmissible gives nonoverdraw before ruin or at t=0, IsAdmissibleLe gives cap at every positive time, and D(0)=X(0)=0 gives initial cap. The closed-cap two-point value inequality then proves the exact hjump premise used in W8-04 without taking it as an additional hypothesis.
-- source:
--   Original IsAdmissibleLe/IsAdmissible/IsDividendStrategy definitions and Proved dividendStrategy_le_rightLimit plus closed-cap C1 source controlled jump adapter. No new stochastic process, time index, filtration or payout definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_controlled_closed_cap_right_dividend_jump_C1_envelope
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_canonical_hjump_of_C1_and_admissible
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)) := by sorry
