-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_all_cap_stopped_terminal_candidate_nonnegative
-- name    : AvramDividend.Classical.avram_wave5_ubv_original_all_cap_stopped_terminal_candidate_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:43:36.349973+00:00
-- url     : https://prove2.me/theorems/c7bf9b3b-8066-4109-a2fc-b9ac81e3ca0f
-- title:
--   Exact corrected UBV candidate is nonnegative at every original reserve including ruin, creeping and zero cap
-- statement:
--   For the actual source SpectrallyNegativeLevy process and its capped admissible dividend control, the corrected UBV separate gradient hypotheses prove w(riskProcess_t)≥0 at every sample time, including any bounded stopping localiser, an actual positive ruin-time endpoint, initial time, and zero cap. First the original cap theorem gives ofReal(U_t)≤C at every time from initial cap and admissibility. If U_t<0 (ruin overshoot) then w(U_t)=0 by the corrected negative zero extension. Otherwise, the accepted closed-cap C2 gradient secant at a=0 gives w(U_t)≥U_t+w(0)≥0. This encompasses continuous creeping through U_t=0 with the indispensable assumption 0≤w(0), without claiming creeping never occurs. Unlike the earlier accepted all-time result 52dd2155-e86a-43fe-bb2e-6f91b3bc9e6f, there is no positive-cap assumption and no BV branch. No Itô-Meyer or dividend Stieltjes result is used.
-- source:
--   Corrected target 429e17ca-5528-40b5-b593-7c03973d0706. Accepted all-time source cap c521fe8f-97c2-40ec-a5c3-b6184a6ad3ea and closed-cap C2 secant 44b01929-5817-44ac-9439-6eb3c9879f2c. Complements exact chronological paid terminal result f72f93f3-cfbf-4a71-b625-a1d0576710c0 without duplicating its postpayment construction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_admissibleLe_riskProcess_le_cap_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_ubv_original_all_cap_stopped_terminal_candidate_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0), 0 ≤ w (riskProcess X x D t ω) := by sorry
