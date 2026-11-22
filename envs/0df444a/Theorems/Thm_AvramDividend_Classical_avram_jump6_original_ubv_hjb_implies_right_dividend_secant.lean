-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_original_ubv_hjb_implies_right_dividend_secant
-- name    : AvramDividend.Classical.avram_jump6_original_ubv_hjb_implies_right_dividend_secant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T18:16:22.594796+00:00
-- url     : https://prove2.me/theorems/9dbbf2f2-bd98-4414-bc95-b3dc25e270b2
-- title:
--   Original UBV HJB max equation implies exact right-dividend jump value drop
-- statement:
--   For an original spectrally negative Lévy source of unbounded variation, the classical HJB maximum equation, interior C² regularity and continuity at zero, and any admissible cap-constrained dividend strategy, prove the exact right-dividend value-drop inequality at time zero and every strict pre-ruin time. The HJB max identity implies the unit slope inequality for the value derivative, including the cap closure by the previously Proved gradient-secant lemma. This removes an extra right-dividend hypothesis from source-faithful stopped Itô–Meyer/conditional budget theorems.
-- source:
--   Avram Dividend Classical mission root-connected 81352a40-fe4f-4cb4-b96f-9705988e553a requires this right-payment inequality to interface with P4 source fdb9a6a3. Proved base 2cd50555-c982-414f-b6aa-527b1d3ba42a (wave5_03); no bounded-variation assumption is introduced.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_separate_gradient_right_atom_control
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_original_ubv_hjb_implies_right_dividend_secant
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)) := by sorry
