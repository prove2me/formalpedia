-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_compact_clock_physical_generator_drift_nonpositive
-- name    : AvramDividend.Classical.avram_f6_original_compact_clock_physical_generator_drift_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:49:56.751165+00:00
-- url     : https://prove2.me/theorems/1eb35b04-bf77-4296-a10c-a28b3941d67d
-- title:
--   Original compact-clock HJB signed generator drift integral is nonpositive
-- statement:
--   For the original spectrally negative Levy driver and actual dividend-controlled prepayment left-limit risk, the discounted HJB generator drift integrated up to the genuine subordinate stopping clock sigma(k) is nonpositive. The physical integrand is exactly the original localised stopped generator X.generator w-qw, masked to the strictly positive below-cap interior; integrability is explicit. No abstract Itô witness, off-cap w regularity, or new stochastic assumption is constructed. This supplies the signed drift component for the common stopped Ito source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_compact_clock_physical_generator_drift_nonpositive
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
        else 0) μ) :
    ∀ ω : Ω,
      (∫ t : ℝ≥0,
        let Y : ℝ := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < Y ∧ ENNReal.ofReal Y < C ∧ t ≤ σ k ω then
          Real.exp (-(q * (t : ℝ))) *
            (X.generator w Y - q * w Y)
        else 0 ∂μ) ≤ 0 := by sorry
