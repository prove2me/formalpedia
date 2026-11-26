-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_actual_jump_product
-- name    : AvramDividend.Classical.avram_locmoll_actual_jump_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:45:55.769587+00:00
-- url     : https://prove2.me/theorems/cb97ed69-f727-57a3-9405-d7e1861c8718
-- title:
--   Actual original test weighted negative generator kernel is product integrable
-- statement:
--   Actual original test weighted negative generator kernel is product integrable
-- source:
--   Avram Proposition 4(i), child of 10e0ec45-30d2-5555-bcde-5adae9d0be9f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_actual_jump_product
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
    Integrable (fun p : ℝ × ℝ => ρ p.1 *
      SpectrallyNegativeLevy.generatorIntegrand w (y - p.1) p.2)
      (volume.prod (X.ν.restrict (Iio 0))) := by sorry
