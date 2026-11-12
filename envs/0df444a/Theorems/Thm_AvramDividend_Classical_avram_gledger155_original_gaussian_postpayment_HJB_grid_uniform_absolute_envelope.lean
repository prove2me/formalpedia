-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger155_original_gaussian_postpayment_HJB_grid_uniform_absolute_envelope
-- name    : AvramDividend.Classical.avram_gledger155_original_gaussian_postpayment_HJB_grid_uniform_absolute_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:21:08.31941+00:00
-- url     : https://prove2.me/theorems/2b76b8f6-963f-49f8-a05e-ab99d7442c88
-- title:
--   Original stopped Gaussian generator finite mesh has a uniform compact L1 envelope
-- statement:
--   The actual stopped postpayment reserve on the strict compact positive band makes the Gaussian generator minus q times payoff uniformly bounded, since ν=0 and w has compact C2 derivatives. Summing over active deterministic mesh cells with total clock at most n gives one deterministic K for all mesh sizes. The measurable source is a separate child.
-- source:
--   Original gledger137 postpayment reserve compact band, true finite stopped mesh and zero-jump Gaussian generator; one source-specific component of gledger153.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger155_original_gaussian_postpayment_HJB_grid_uniform_absolute_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation)
    (hSigmaNonzero : X.σ ≠ 0) (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧ riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let G : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1); Finset.sum (Finset.range m) (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then
          let y := x + X.X s ω - rightLimit D s ω
          (Δ : ℝ) * Real.exp (-(q * (s : ℝ))) * (X.generator w y - q * w y)
        else 0)
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, ∀ᵐ ω ∂P, |G m ω| ≤ K := by sorry
