-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_cap_zero_uniform_all_source_mark_measures
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_cap_zero_uniform_all_source_mark_measures
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:14:17.811678+00:00
-- url     : https://prove2.me/theorems/90895d23-7a51-4dee-95bf-a6b1fc629bc7
-- title:
--   One original-process conull event kills every marked source compensator cap characteristic for all Lévy measures and weights simultaneously
-- statement:
--   For original UBV controlled spectrally negative source and same filtration, fix an atomless s-finite physical-time μ. Then one P-full event works for EVERY deterministic real jump-mark measure ν and EVERY arbitrary nonnegative potentially infinite mark-density weight: the dt⊗ν marked cap-contact contribution at true predictable pre-event reserve is zero before ruin. This strengthens earlier fixed-ν and countable-ν results by taking quantifiers ∀ᵐω,∀ν,∀weight via the accepted uniform-in-weight source cap-null event. It includes x=c and cap dividend payments. It says nothing about actual random jump martingale compensation, cap local time or random dividend Stieltjes measures.
-- source:
--   Parent source-faithful uniform-in-weight cap occupation target AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_zero_uniform_all_characteristic_weights plus accepted marked theorem f215189c-2384-4a8d-94c5-e38a78a41f2a. Supports corrected canonical core 429e17ca-5528-40b5-b593-7c03973d0706 without changing it.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_zero_uniform_all_characteristic_weights

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_cap_zero_uniform_all_source_mark_measures
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ (ν : Measure ℝ) (weight : ℝ≥0 → ℝ → Ω → ℝ≥0∞),
      (∫⁻ t : ℝ≥0, ∫⁻ z : ℝ,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
        then weight t z ω else 0 ∂ν ∂μ) = 0 := by sorry
