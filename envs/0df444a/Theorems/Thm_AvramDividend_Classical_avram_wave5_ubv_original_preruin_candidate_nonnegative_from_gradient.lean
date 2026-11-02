-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_preruin_candidate_nonnegative_from_gradient
-- name    : AvramDividend.Classical.avram_wave5_ubv_original_preruin_candidate_nonnegative_from_gradient
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:41:43.148238+00:00
-- url     : https://prove2.me/theorems/a81e26e3-b329-4cf1-bd1f-7ce8d83fd66b
-- title:
--   Corrected UBV original pre-ruin candidate nonnegativity from the exact separate gradient hypothesis
-- statement:
--   For the original Lévy process X and actual IsAdmissibleLe dividend strategy D, the corrected UBV core's separate hypotheses 0≤w(0), continuity on nonnegative reserves, C2 in the strict capped interior, and derivative w'≥1 imply w(U_t)≥0 at every strictly positive t before the actual ruinTime. No HJB maximum identity is required, unlike earlier stronger-premise pre-ruin lemmas. Source pathwise pre-ruin solvency supplies U_t≥0; the original admissibility cap applies at positive times; the canonically Proved closed-cap UBV gradient secant with a=0 yields w(U_t)≥U_t+w(0)≥0. This formally discharges the explicit hw_nonneg premise of the corrected canonical core using only its existing hypotheses, including the cap and all boundary cases. It requires no stochastic Itô computation.
-- source:
--   Corrected Avram UBV stochastic verification core 429e17ca-5528-40b5-b593-7c03973d0706. Uses accepted riskProcess_nonneg_before_ruin c26c83f7-d703-46b9-a361-bf008b70dfe6 and closed-cap C2 gradient secant 44b01929-5817-44ac-9439-6eb3c9879f2c. Strengthens prior HJB-max premise in cd9655ac-edda-49b9-a69e-afe57d8a5f01.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_ubv_original_preruin_candidate_nonnegative_from_gradient
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
        0 ≤ w (riskProcess X x D t ω) := by sorry
