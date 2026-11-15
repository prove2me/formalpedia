-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a326_original_true_large_combined_positive_source_integrable
-- name    : AvramDividend.Classical.avram_ga_a326_original_true_large_combined_positive_source_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T11:02:45.761029+00:00
-- url     : https://prove2.me/theorems/fdc60594-eb0b-4937-8701-23ff12637c3b
-- title:
--   True original Gaussian stopped physical rare combined HJB positive source integrable for every mesh and cutoff
-- statement:
--   For every original zerojump Gaussian physically fully stopped mesh and positive rare raw increment cutoff, the positive part of the complete combined discounted verification residual is Bochner integrable. Source a323 proves almost-sure strong measurability under the actual stopped-and-rare masks, a319 bounds the source almost surely by positive constants times the exact signed Gaussian exponential and original raw/centered polynomial rare tails, both integrable by a320, and a325 transfers integrability. This supplies the finite-mesh integrability half of the original large-cell a263 parent.
-- source:
--   Original a319/a320/a323 and generic integrability majorant a325.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a319_original_true_fullcell_rare_positive_two_source_all_mesh_bound
import Theorems.Thm_AvramDividend_Classical_avram_ga_a320_original_true_fullcell_signed_and_polynomial_rare_two_L1_package
import Theorems.Thm_AvramDividend_Classical_avram_ga_a325_nonnegative_measurable_Gaussian_source_integrable_two_positive_tail_majorant
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a326_original_true_large_combined_positive_source_integrable
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
    ∀ δ : ℝ, 0 < δ → ∀ m,
      Integrable (fun ω => max (Large δ m ω) 0) P := by sorry
