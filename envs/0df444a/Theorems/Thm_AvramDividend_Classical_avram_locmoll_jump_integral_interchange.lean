-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_jump_integral_interchange
-- name    : AvramDividend.Classical.avram_locmoll_jump_integral_interchange
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T20:23:08.507393+00:00
-- url     : https://prove2.me/theorems/10e0ec45-30d2-5555-bcde-5adae9d0be9f
-- title:
--   Weighted negative-mark generator integral: Taylor domination and Fubini
-- statement:
--   Weighted negative-mark generator integral: Taylor domination and Fubini
-- source:
--   Avram Proposition 4(i), exact decomposition of 4ce72d47-4d5a-479e-bf24-f651ec5f67ec

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_jump_integral_interchange
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
    (hg : ContDiff ℝ 2 (fun y => ∫ r, ρ r * V (y - r)))
    (y : ℝ) (hy : δ ≤ y) (hyC : ENNReal.ofReal y ≤ C)
    (hD1 : Integrable (fun r => ρ r * deriv w (y - r)))
    (hd1 : deriv (fun t => ∫ r, ρ r * V (t - r)) y =
      (∫ r, ρ r * deriv w (y - r))) :
    X.GeneratorIntegrable (fun t => ∫ r, ρ r * V (t - r)) y ∧
    Integrable (fun r => ρ r * (∫ z in Iio (0 : ℝ), SpectrallyNegativeLevy.generatorIntegrand w (y - r) z ∂X.ν)) ∧
    (∫ z in Iio (0 : ℝ), SpectrallyNegativeLevy.generatorIntegrand
      (fun t => ∫ r, ρ r * V (t - r)) y z ∂X.ν) =
    (∫ r, ρ r * (∫ z in Iio (0 : ℝ),
      SpectrallyNegativeLevy.generatorIntegrand w (y - r) z ∂X.ν)) := by sorry
