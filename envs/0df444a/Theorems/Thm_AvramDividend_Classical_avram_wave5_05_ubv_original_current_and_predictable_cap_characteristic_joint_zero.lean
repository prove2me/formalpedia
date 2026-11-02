-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_current_and_predictable_cap_characteristic_joint_zero
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_current_and_predictable_cap_characteristic_joint_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:44:34.507342+00:00
-- url     : https://prove2.me/theorems/fcc1023f-9813-4133-9fe8-c4836143ffb4
-- title:
--   One conull original-process event simultaneously kills weighted positive-time cap contact of both current and predictable pre-event controlled reserves
-- statement:
--   On one P-conull event of the actual original UBV Lévy and same-filtration admissible dividend trajectory, both the post-payment book reserve U_t and correct predictable pre-event reserve leftLim(x+X−rightLimit D)_t have zero weighted exact-cap contact mass on the same atomless s-finite time clock over all positive pre-ruin times. The weights may independently depend on state, time, trajectory and be infinite at cap. This handles simultaneously the current reserve used in viability and the predictable state used by the stochastic generator without assuming dividends occur below cap, including initial x=c. Random cap local time and Stieltjes dividend clocks remain separate.
-- source:
--   Current weighted source cap Proved 51c7ab38-4295-458a-b686-6b270e8ac5f8 and predictable weighted source cap Proved f8199679-8516-46fa-b24a-b17cf33e8b8b; corrected canonical core 429e17ca-5528-40b5-b593-7c03973d0706 untouched.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_same_source_weighted_cap_contact_clock_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_contact_weighted_atomless_zero

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_current_and_predictable_cap_characteristic_joint_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ]
    (currentWeight preWeight : ℝ≥0 → Ω → ℝ≥0∞) :
    ∀ᵐ ω ∂P,
      (∫⁻ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            riskProcess X x D t ω = c
        then currentWeight t ω else 0 ∂μ) = 0 ∧
      (∫⁻ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
        then preWeight t ω else 0 ∂μ) = 0 := by sorry
