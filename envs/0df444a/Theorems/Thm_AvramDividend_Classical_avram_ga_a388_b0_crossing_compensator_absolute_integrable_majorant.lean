-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a388_b0_crossing_compensator_absolute_integrable_majorant
-- name    : AvramDividend.Classical.avram_ga_a388_b0_crossing_compensator_absolute_integrable_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T14:16:11.0782+00:00
-- url     : https://prove2.me/theorems/3f7b736c-69ca-41cc-8be6-1f8aad22aa3a
-- title:
--   A common L1 majorant for actual strict-crossing Gaussian compensated HJB generator cell
-- statement:
--   An integrable random envelope dominates in absolute value the original masked Gaussian compensated HJB and generator term on the unique strictly crossing cell at every mesh size.
-- source:
--   Original a385 true crossing common integrable envelope split into spatial and compensator source exact components; a44, a40, a143, a127 provide proved abstract envelope tools.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a388_b0_crossing_compensator_absolute_integrable_majorant
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
    let Comp : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if CrossMask m i ω then
          let z := X.X (s m i + Δ m) ω - X.X (s m i) ω - (Δ m : ℝ) * X.c
          E (s m i) * (deriv w (Y ω (s m i)) * z +
            (iteratedDeriv 2 w (Y ω (s m i)) / 2) *
              (z^2 - (Δ m : ℝ) * X.σ^2)) +
            (Δ m : ℝ) * E (s m i) * X.generator w (Y ω (s m i))
        else 0
    ∃ B : Ω → ℝ, Integrable B P ∧
      ∀ (m : ℕ), ∀ᵐ ω ∂P, ‖Comp m ω‖ ≤ B ω := by sorry
