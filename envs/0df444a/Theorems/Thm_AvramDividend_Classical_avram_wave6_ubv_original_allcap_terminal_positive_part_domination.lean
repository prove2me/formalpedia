-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_ubv_original_allcap_terminal_positive_part_domination
-- name    : AvramDividend.Classical.avram_wave6_ubv_original_allcap_terminal_positive_part_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:38:05.235362+00:00
-- url     : https://prove2.me/theorems/2b04d61b-0c38-44e4-ba16-ea6843d0c45e
-- title:
--   Original all-cap UBV stopped reserve terminal candidate dominates positive part
-- statement:
--   For the actual source SpectrallyNegativeLevy P 𝓕, all-cap admissible D, and the corrected 0≤w(0), continuity and strictly interior gradient assumptions, w applied to the actual reserve at any time dominates max(0,reserve). At a creeping zero the comparison is w(0)≥0, at negative overshoot w=0, and at nonnegative reserve the previously Proved inclusive secant inequality supplies w(y)≥y+w(0)≥y. No boundary derivative, C² at zero, bounded-variation, or filtration change is introduced.
-- source:
--   Accepted all-cap terminal nonnegativity c7bf9b3b-8066-4109-a2fc-b9ac81e3ca0f; accepted original all-cap gradient secant 44b01929-5817-44ac-9439-6eb3c9879f2c; corrected core 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_admissibleLe_riskProcess_le_cap_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_all_cap_stopped_terminal_candidate_nonnegative

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_ubv_original_allcap_terminal_positive_part_domination
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
      max 0 (riskProcess X x D t ω) ≤ w (riskProcess X x D t ω) := by sorry
