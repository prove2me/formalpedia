-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a541_original_clipped_single_value_aestronglyMeasurable
-- name    : AvramDividend.Classical.avram_ga_a541_original_clipped_single_value_aestronglyMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:39:14.244782+00:00
-- url     : https://prove2.me/theorems/69f206d9-ad43-4c54-a566-948eaa27e732
-- title:
--   Individual original clipped spatial cell is a.e. measurable, including inactive cancellation
-- statement:
--   Under the original stopped Gaussian hypotheses, each individually masked clipped postpayment value-difference cell is a.e. strongly measurable even when the value function is only continuous on positive reserves, by cancellation on zero-clock paths.
-- source:
--   Apply the Proved a43 original clipped spatial observations, a158 continuity and a535 active positive-domain one-cell measurability, then cancel the zero-clock branch.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a541_original_clipped_single_value_aestronglyMeasurable
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
    let A : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun a => min ((a : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun a =>
        x + X.X (v (a + 1)) ω - rightLimit D (v a) ω
      if 0 < ρ ω then E (v (i + 1)) * (w (Z i) - w (Y (v i)))
      else 0
    ∀ m i : ℕ, i < m → AEStronglyMeasurable (A m i) P := by sorry
