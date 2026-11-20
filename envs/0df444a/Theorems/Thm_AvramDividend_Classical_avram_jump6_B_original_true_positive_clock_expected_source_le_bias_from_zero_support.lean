-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_true_positive_clock_expected_source_le_bias_from_zero_support
-- name    : AvramDividend.Classical.avram_jump6_B_original_true_positive_clock_expected_source_le_bias_from_zero_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:34:44.885617+00:00
-- url     : https://prove2.me/theorems/3367452e-f588-429c-a43c-1cc01e10f331
-- title:
--   Exact true stopped physical source expected upper bound on positive-clock event with deterministic bias and zero-clock source support
-- statement:
--   The original stopped Levy physical source S=M+Q+bias has global mean bounded by bias from exact HJB generator sign and centered M. If the true source itself vanishes on zero-clock paths, its positive-clock event integral equals its global integral, so the exact event source expected upper bound remains bias. This route correctly allows the canonical centring M=-bias on zero-clock paths; no incorrect eventwise centered M assumption is needed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_physical_centered_source_expected_upper_by_bias
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_original_true_positive_clock_expected_source_le_bias_from_zero_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (σ : Ω → ℝ≥0) (hσmeas : Measurable σ) (u : ℕ → ℕ → ℝ≥0) (m : ℕ → ℕ)
    (Source M Q : ℕ → Ω → ℝ) (bias : ℕ → ℝ)
    (hQphysical : ∀ j ω,
      Q j ω = (let v : ℕ → ℝ≥0 := fun i => min (u j i) (σ ω)
        let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
        let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
        ∑ i ∈ Finset.range (m j),
          E (v (i + 1)) * (((v (i + 1) - v i : ℝ≥0) : ℝ)) *
            (if 0 < Y (v i) ∧ ENNReal.ofReal (Y (v i)) < C then
              X.generator w (Y (v i)) - q * w (Y (v i))
             else 0)))
    (hM : ∀ j, Integrable (M j) P)
    (hQ : ∀ j, Integrable (Q j) P)
    (hMzero : ∀ j, (∫ ω, M j ω ∂P) = 0)
    (hSource : ∀ j ω, Source j ω = M j ω + Q j ω + bias j)
    (hZero : ∀ j ω, σ ω = 0 → Source j ω = 0) :
    ∀ j, (∫ ω in {ω | 0 < σ ω}, Source j ω ∂P) ≤ bias j := by sorry
