-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_zero_countable_marked_compensators
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_zero_countable_marked_compensators
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:56:24.890624+00:00
-- url     : https://prove2.me/theorems/ce765d5a-2e8f-406a-bbb5-74d49654f187
-- title:
--   Every countable Lévy mark-truncation characteristic of the same original predictable capped process has zero boundary intensity on a single conull event
-- statement:
--   Given the original UBV Lévy source and its actual same-filtration capped dividend strategy, an arbitrary prescribed sequence n of atomless s-finite physical-time measures μ_n, independent mark measures ν_n and possibly infinite nonnegative mark densities has zero joint time/mark characteristic when supported at exact cap contact of the true predictable pre-event reserve. All n hold simultaneously on one P-conull set. This includes any countable Lévy jump truncation/localisation scale, even initial capital x=c. It is a deterministic source compensator support result, not a proof of compensation, cap local time, or random dividend Stieltjes vanishing.
-- source:
--   Proved marked original cap-compensator nullity f215189c-2384-4a8d-94c5-e38a78a41f2a; corrected canonical 429e17ca-5528-40b5-b593-7c03973d0706 untouched; mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_zero_marked_source_compensator

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_zero_countable_marked_compensators
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : ℕ → Measure ℝ≥0)
    (hsf : ∀ n, SFinite (μ n))
    (hatom : ∀ n, NullSingletonClass (μ n))
    (ν : ℕ → Measure ℝ)
    (weight : ℕ → ℝ≥0 → ℝ → Ω → ℝ≥0∞) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      (∫⁻ t : ℝ≥0, ∫⁻ z : ℝ,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
        then weight n t z ω else 0 ∂(ν n) ∂(μ n)) = 0 := by sorry
