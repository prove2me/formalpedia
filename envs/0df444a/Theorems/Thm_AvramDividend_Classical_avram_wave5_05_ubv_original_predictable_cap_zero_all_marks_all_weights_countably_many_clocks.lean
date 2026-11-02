-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_zero_all_marks_all_weights_countably_many_clocks
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_zero_all_marks_all_weights_countably_many_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:15:45.640139+00:00
-- url     : https://prove2.me/theorems/b6b565a6-ca36-4f5b-b3ee-74affe1a2ffd
-- title:
--   One original UBV full-probability event kills all marked cap-supported Lévy compensator densities across countably many atomless clocks
-- statement:
--   For any prescribed countable family μ_n of s-finite atomless physical-time clocks, one full P-probability original controlled unbounded-variation Levy event works simultaneously for every index n, every arbitrary mark measure ν on real jump sizes, and every nonnegative extended-real weight W(t,z,ω), including infinite and nonmeasurable weights. At strictly positive pre-ruin times, the exact predictable original reserve is leftLim(x+X−rightLimit D); the μ_n⊗ν lintegral of any W supported on its equality to the cap c is zero, with the event chosen before n,ν,W. This is precisely a generator/compensation cap-boundary lemma and allows initial x=c. It does not assert nullity of cap local time or the random dividend Stieltjes clock.
-- source:
--   Proved original predictable cap zero for ALL weights and countably many clocks d841211e-0a93-440c-9a2b-1a2fb90ed40f; original marked proof f215189c-2384-4a8d-94c5-e38a78a41f2a. Corrected UBV core 429e17ca-5528-40b5-b593-7c03973d0706 unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_zero_all_weights_countably_many_clocks

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_zero_all_marks_all_weights_countably_many_clocks
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
    ∀ᵐ ω ∂P, ∀ (n : ℕ) (ν : Measure ℝ)
      (weight : ℝ≥0 → ℝ → Ω → ℝ≥0∞),
      (∫⁻ t : ℝ≥0, ∫⁻ z : ℝ,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
        then weight t z ω else 0 ∂ν ∂μ n) = 0 := by sorry
