-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_signed_generator_cap_patch_countable_clocks
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_signed_generator_cap_patch_countable_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:28:46.055825+00:00
-- url     : https://prove2.me/theorems/9c4c8f46-0641-46bf-ad56-2597d3f2e4d9
-- title:
--   One original UBV event makes signed generator cap-value patches invisible on every prescribed countable atomless physical-time clock
-- statement:
--   For the genuine capped original spectrally negative UBV Levy reserve and any countably prescribed SFinite atomless physical-time clocks μ_n, there exists one P-full event such that, for EVERY n and EVERY two arbitrary real-valued generator drift densities F,G selected after ω, if their only possible differences on positive surviving times occur at exact true predictable cap contact, their stopped ordinary real integrals with respect to μ_n coincide. This is cap-boundary invariance for signed HJB drifts simultaneously over countable stochastic localisation clocks. Initial reserve equal to the cap is allowed. It assumes neither a cap derivative nor dividends strictly below the cap, and does not eliminate singular cap local time or dividend Stieltjes mass.
-- source:
--   Parent signed generator patch target (publication pending) from work/avram_wave5_prejump_signed_generator_patch_independence_20261101_spec.json; original source occupation cc500549-ba08-47b0-b5c0-07c7a9bb40f3; corrected core 429e17ca-5528-40b5-b593-7c03973d0706 unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_signed_generator_cap_value_patch_integral_independence

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_signed_generator_cap_patch_countable_clocks
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
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ (F G : ℝ≥0 → Ω → ℝ),
      (∀ t : ℝ≥0, 0 < t →
        (t : ℝ≥0∞) < ruinTime X x D ω →
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ≠ c →
        F t ω = G t ω) →
      (∫ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω
        then F t ω else 0 ∂μ n) =
      (∫ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω
        then G t ω else 0 ∂μ n) := by sorry
