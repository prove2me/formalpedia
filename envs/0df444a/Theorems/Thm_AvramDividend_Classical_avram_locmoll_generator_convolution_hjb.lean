-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_generator_convolution_hjb
-- name    : AvramDividend.Classical.avram_locmoll_generator_convolution_hjb
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T19:58:56.526563+00:00
-- url     : https://prove2.me/theorems/4ce72d47-4d5a-479e-bf24-f651ec5f67ec
-- title:
--   One-sided convolution preserves the original spectrally negative Lévy HJB drift
-- statement:
--   The general jump-generator interchange uses compact interior derivative bounds, finite mass away from zero, and Fubini, relying on negative jump marks and exact agreement of the cap extension on arguments below the cap.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), child of 2e269e44-0ec4-4d09-bac9-26533bf1d8ab

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_generator_convolution_hjb
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (w V ρ : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (δ : ℝ) (hδ : 0 < δ)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hVeq : ∀ y : ℝ, ENNReal.ofReal y ≤ C → V y = w y)
    (hVmono : Monotone V) (hVnonneg : ∀ y, 0 ≤ V y)
    (hVzero : ∀ y < 0, V y = 0)
    (hρI : Integrable ρ) (hρnorm : (∫ r, ρ r) = 1)
    (hρpos : 0 ≤ᵐ[volume] ρ)
    (hρsupport : ∀ᵐ r ∂volume, ρ r ≠ 0 →
      r ∈ Icc (δ / 3) (2 * (δ / 3)))
    (hρsmooth : ContDiff ℝ 2 ρ) (hρcompact : HasCompactSupport ρ)
    (hI : ∀ y : ℝ, Integrable (fun r => ρ r * V (y - r)))
    (hg : ContDiff ℝ 2 (fun y => ∫ r, ρ r * V (y - r))) :
    ∀ y : ℝ, δ ≤ y → ENNReal.ofReal y ≤ C →
      X.GeneratorIntegrable (fun t => ∫ r, ρ r * V (t - r)) y ∧
      X.generator (fun t => ∫ r, ρ r * V (t - r)) y -
        q * (∫ r, ρ r * V (y - r)) ≤ 0 := by sorry
