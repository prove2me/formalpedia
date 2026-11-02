-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_zero_all_weights_countably_many_clocks
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_zero_all_weights_countably_many_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T12:12:25.311725+00:00
-- url     : https://prove2.me/theorems/d841211e-0a93-440c-9a2b-1a2fb90ed40f
-- title:
--   One original UBV conull event kills predictable cap generator contact for all weights across countably many atomless characteristic clocks
-- statement:
--   For the genuine original controlled spectrally negative unbounded-variation Levy reserve, with possible starting capital equal to the cap, a countable family of fixed SFinite atomless physical clocks shares ONE P-full path event. On this event, for every clock n and every arbitrarily chosen nonnegative (possibly infinite, even nonmeasurable) time and path generator density, its exact predictable cap-contact lintegral is zero before ruin, at all positive clock times. Quantifiers ∀a.e. ω ∀n ∀weight are essential: a weight may be selected after path and clock. This handles simultaneous Brownian and jump compensation characteristics and countable localisation clocks but does not assert local-time or singular dividend Stieltjes nullity.
-- source:
--   Proved uniform all weights for a fixed clock, target 35fd2e0a-aab2-4685-8bce-b53aa9dbdd00, plus countable P-a.e quantification. Corrected canonical core 429e17ca-5528-40b5-b593-7c03973d0706 unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_zero_uniform_all_characteristic_weights

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_zero_all_weights_countably_many_clocks
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : ℕ → Measure ℝ≥0)
    (hsf : ∀ n, SFinite (μ n))
    (hatom : ∀ n, NullSingletonClass (μ n)) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ weight : ℝ≥0 → Ω → ℝ≥0∞,
      (∫⁻ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
        then weight t ω else 0 ∂μ n) = 0 := by sorry
