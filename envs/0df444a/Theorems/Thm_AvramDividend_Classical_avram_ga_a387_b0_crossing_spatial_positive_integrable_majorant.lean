-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a387_b0_crossing_spatial_positive_integrable_majorant
-- name    : AvramDividend.Classical.avram_ga_a387_b0_crossing_spatial_positive_integrable_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T14:16:14.068479+00:00
-- url     : https://prove2.me/theorems/d7699e58-084b-406c-bd75-d6ad5d4d5b6b
-- title:
--   A common L1 majorant for actual strict-crossing stopped Gaussian spatial value positive part
-- statement:
--   An integrable random envelope dominates the one genuinely crossing cell of the original stopped discounted Gaussian spatial value increment at every physical mesh size.
-- source:
--   Original a385 true crossing common integrable envelope split into spatial and compensator source exact components; a44, a40, a143, a127 provide proved abstract envelope tools.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a387_b0_crossing_spatial_positive_integrable_majorant
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
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : Ω → ℝ≥0 → ℝ := fun ω t => x + X.X t ω - rightLimit D t ω
    let CrossMask : ℕ → ℕ → Ω → Prop := fun m i ω =>
      s m i < ρ ω ∧ ρ ω < s m i + Δ m
    let Spatial : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if CrossMask m i ω then
          E (ρ ω) * (w (Y ω (s m i) +
            (X.X (ρ ω) ω - X.X (s m i) ω)) - w (Y ω (s m i)))
        else 0
    ∃ B : Ω → ℝ, Integrable B P ∧
      ∀ (m : ℕ), ∀ᵐ ω ∂P, ‖max (Spatial m ω) 0‖ ≤ B ω := by sorry
