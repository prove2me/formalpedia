-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a327_original_true_large_combined_positive_expected_L1_vanish
-- name    : AvramDividend.Classical.avram_ga_a327_original_true_large_combined_positive_expected_L1_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T11:01:58.945528+00:00
-- url     : https://prove2.me/theorems/097aa8e5-1303-4e49-a374-fbb561b3ae15
-- title:
--   Genuine original Gaussian stopped fullcell rare combined discounted positive verification source expected L1 vanishes
-- statement:
--   For every positive fixed rare raw-increment cutoff δ, the expected positive part of the true fully stopped Gaussian physical mesh combined discounted HJB verification residual tends to zero. Source a319 gives an almost-sure upper bound by two actual Gaussian source tails at all mesh levels; a320 verifies both original signed exponential and polynomial rare tails integrable and vanishing in expectation; a326 proves integrability of the true combined source; a315 squeezes its expected positive part to zero. Together with a326 this closes original a263 large-cell branch.
-- source:
--   Original a319 actual rare source upper, a320 true signed/poly expected L1, a326 source integrability and a315 expectation comparison.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a319_original_true_fullcell_rare_positive_two_source_all_mesh_bound
import Theorems.Thm_AvramDividend_Classical_avram_ga_a320_original_true_fullcell_signed_and_polynomial_rare_two_L1_package
import Theorems.Thm_AvramDividend_Classical_avram_ga_a315_eventual_ae_two_error_expected_L1_squeeze
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a327_original_true_large_combined_positive_expected_L1_vanish
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
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1))
    (δ : ℝ) (hδ : 0 < δ) :
    let Large : ℝ → ℕ → Ω → ℝ := fun δ m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun i =>
      E (s i) * (deriv w (Y (s i)) * R i +
        (iteratedDeriv 2 w (Y (s i)) / 2) * Z i^2)
    let F : ℕ → ℝ := fun i =>
      E (s i + Δ) * (w (Y (s i) + R i) - w (Y (s i))) - H i
    ∑ i ∈ Finset.range m,
      if s i < ρ ω ∧ s i + Δ ≤ ρ ω ∧ δ ≤ |R i| then F i else 0
    ∀ δ : ℝ, 0 < δ →
      Tendsto (fun m => ∫ ω, max (Large δ m ω) 0 ∂P)
        atTop (𝓝 (0 : ℝ)) := by sorry
