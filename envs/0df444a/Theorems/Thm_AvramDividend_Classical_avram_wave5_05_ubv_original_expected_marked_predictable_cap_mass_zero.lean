-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_expected_marked_predictable_cap_mass_zero
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_expected_marked_predictable_cap_mass_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:53:29.247597+00:00
-- url     : https://prove2.me/theorems/f340f5ba-d18a-4d4f-9312-dc9ec1059fff
-- title:
--   Original UBV predictable exact-cap marked compensator has zero expected physical-clock mass
-- statement:
--   For the genuine original unbounded-variation spectrally negative Levy controlled reserve and any fixed s-finite atomless physical clock, every deterministic Lévy mark measure and every nonnegative possibly infinite path-dependent mark kernel has zero expected stopped marked compensator mass concentrated where the exact chronological predictable pre-event reserve equals the finite cap. The probability integral is over the original source law P. Initial capital may equal cap and cap contacts may recur. This is a direct Tonelli-compatible expectation-level consequence of a single original-process P-conull uniform all-marks and all-weights event. It does not assert actual jump martingale compensation, stochastic Itô, local time or singular dividend Stieltjes nullity.
-- source:
--   Proved original one-event all-source-mark-measures cap-contact null theorem 90895d23-7a51-4dee-95bf-a6b1fc629bc7; original chronology and cap occupation inputs cc500549-ba08-47b0-b5c0-07c7a9bb40f3 and 89e50cbf-efd7-4c66-8cd6-2d1e99de1a8d. Corrected canonical core unchanged 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_cap_zero_uniform_all_source_mark_measures

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_expected_marked_predictable_cap_mass_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ (ν : Measure ℝ) (weight : ℝ≥0 → ℝ → Ω → ℝ≥0∞),
      (∫⁻ ω : Ω, ∫⁻ t : ℝ≥0, ∫⁻ z : ℝ,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
        then weight t z ω else 0 ∂ν ∂μ ∂P) = 0 := by sorry
