-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_allcap_actual_right_payment_secant_nonpos
-- name    : AvramDividend.Classical.avram_wave6_04b_allcap_actual_right_payment_secant_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:14:55.304202+00:00
-- url     : https://prove2.me/theorems/f3d90ee0-9e69-409d-989f-f4c8103817ff
-- title:
--   All-positive-cap actual chronological right dividend payment nonpositive secant
-- statement:
--   For the original Lévy reserve regulated by an admissible dividend strategy under any positive ENNReal cap, every right-payment jump at t=0 or a pre-ruin time has a nonpositive derivative-free cap-extension potential correction. The source left jump is applied before the right dividend payment. Post-payment solvency and dividend monotonicity supply the secant endpoints. No strict interior reserve occupation, endpoint derivative or separate explicit jump-drop hypothesis is assumed.
-- source:
--   import Mathlib
--   import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
--   import Definitions.Def_AvramDividend_Classical_DividendStrategy
--   import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
--   import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
--
--   open MeasureTheory Set
--   open scoped NNReal ENNReal
--   open AvramDividend.Classical
--
--   set_option pp.explicit true
--   set_option pp.fullNames true
--   set_option pp.universes true
--
--   /-- Actual chronological right dividend payment correction is nonpositive
--   for every positive finite/infinite cap, including zero and cap contacts. -/
--   theorem AvramDividend.Classical.avram_wave6_04b_allcap_actual_right_payment_secant_nonpos
--       {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
--       {𝓕 : Filtration ℝ≥0 mΩ}
--       (X : SpectrallyNegativeLevy P 𝓕)
--       (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
--       (w V : ℝ → ℝ)
--       (hw_cont : ContinuousOn w (Ici 0))
--       (hw_smooth : ContDiffOn ℝ 1 w
--         {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
--       (hw_grad : ∀ y : ℝ, 0 < y →
--         ENNReal.ofReal y < C → 1 ≤ deriv w y)
--       (hVtop : C = ⊤ → ∀ y : ℝ, V y = w y)
--       (hVfinite : C ≠ ⊤ → ∀ y : ℝ,
--         V y = if y ≤ C.toReal then w y
--           else w C.toReal + (y - C.toReal))
--       (D : ℝ≥0 → Ω → ℝ)
--       (hD : IsAdmissibleLe X x C D)
--       (ω : Ω) (t : ℝ≥0)
--       (hPre : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
--       (rightLimit D t ω - D t ω) +
--         V (riskProcess X x D t ω -
--           (rightLimit D t ω - D t ω)) -
--         V (riskProcess X x D t ω) ≤ 0 := by
--     have hAdmissible : IsAdmissible X x D := hD.1
--     have hStrategy : IsDividendStrategy 𝓕 D := hAdmissible.1
--     let U : ℝ := riskProcess X x D t ω
--     let δ : ℝ := rightLimit D t ω - D t ω
--     have hpay : 0 ≤ δ := sub_nonneg.mpr
--       (dividendStrategy_le_rightLimit D hStrategy ω t)
--     have hpost : 0 ≤ U - δ := by
--       have hs := hAdmissible.2 ω t hPre
--       change δ ≤ U at hs
--       linarith only [hs]
--     have horder : U - δ ≤ U := by linarith only [hpay]
--     have hsec := avram_wave5_04b_positive_ennreal_cap_extension_global_secant
--       C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
--       (U - δ) U hpost horder
--     change δ + V (U - δ) - V U ≤ 0
--     linarith only [hsec]

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave6_04b_allcap_actual_right_payment_secant_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hVtop : C = ⊤ → ∀ y : ℝ, V y = w y)
    (hVfinite : C ≠ ⊤ → ∀ y : ℝ,
      V y = if y ≤ C.toReal then w y
        else w C.toReal + (y - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (hPre : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    (rightLimit D t ω - D t ω) +
      V (riskProcess X x D t ω -
        (rightLimit D t ω - D t ω)) -
      V (riskProcess X x D t ω) ≤ 0 := by sorry
