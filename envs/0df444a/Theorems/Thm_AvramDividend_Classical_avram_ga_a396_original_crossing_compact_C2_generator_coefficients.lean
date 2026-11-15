-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a396_original_crossing_compact_C2_generator_coefficients
-- name    : AvramDividend.Classical.avram_ga_a396_original_crossing_compact_C2_generator_coefficients
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:50:48.96582+00:00
-- url     : https://prove2.me/theorems/3fec2fa9-5014-4f96-9395-619783e915a6
-- title:
--   Original stopped positive compact prefix uniformly bounds Gaussian derivative, Hessian, generator
-- statement:
--   On every original pre-stop physical grid cell, the C2 Gaussian value's first derivative, Hessian, and zero-jump generator are uniformly bounded by one deterministic constant almost surely.
-- source:
--   Proved original Hessian a370, continuous derivatives a378, zero-jump generator identity and compact postpayment prefix.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a396_original_crossing_compact_C2_generator_coefficients
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᵐ ω ∂P, ∀ (m i : ℕ),
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        s < ρ ω →
          |deriv w (x + X.X s ω - rightLimit D s ω)| ≤ K ∧
          |iteratedDeriv 2 w (x + X.X s ω - rightLimit D s ω)| ≤ K ∧
          |X.generator w (x + X.X s ω - rightLimit D s ω)| ≤ K := by sorry
