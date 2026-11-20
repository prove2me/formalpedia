-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_compact_clock_physical_generator_expected_nonpositive
-- name    : AvramDividend.Classical.avram_f6_original_compact_clock_physical_generator_expected_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:53:26.264655+00:00
-- url     : https://prove2.me/theorems/340d73f0-3cef-4649-ae15-61718b64fe7e
-- title:
--   Original true-clock integrated HJB generator drift has nonpositive expectation
-- statement:
--   For the original spectrally negative Levy driver, original dividend-controlled predictable prepayment state and each true subordinate clock sigma(k), the actual discounted HJB generator drift is nonpositive in pathwise time and therefore in expectation whenever the physical time and probability integrals are integrable. The source is the original generator w on strictly interior positive below-cap states with exact cutoff mask. This handles the genuine signed generator channel without imaginary martingale witnesses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_compact_clock_physical_generator_expected_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (D : ℝ≥0 → Ω → ℝ)
    (σ : ℕ → Ω → ℝ≥0) (k : ℕ) (μ : Measure ℝ≥0)
    (hGInt : ∀ ω : Ω, Integrable
      (fun t : ℝ≥0 =>
        let Y : ℝ := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < Y ∧ ENNReal.ofReal Y < C ∧ t ≤ σ k ω then
          Real.exp (-(q * (t : ℝ))) *
            (X.generator w Y - q * w Y)
        else 0) μ)
    (hGI : Integrable (fun ω : Ω => (∫ t : ℝ≥0,
        let Y : ℝ := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < Y ∧ ENNReal.ofReal Y < C ∧ t ≤ σ k ω then
          Real.exp (-(q * (t : ℝ))) *
            (X.generator w Y - q * w Y)
        else 0 ∂μ)) P) :
    (∫ ω : Ω, (∫ t : ℝ≥0,
        let Y : ℝ := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < Y ∧ ENNReal.ofReal Y < C ∧ t ≤ σ k ω then
          Real.exp (-(q * (t : ℝ))) *
            (X.generator w Y - q * w Y)
        else 0 ∂μ) ∂P) ≤ 0 := by sorry
