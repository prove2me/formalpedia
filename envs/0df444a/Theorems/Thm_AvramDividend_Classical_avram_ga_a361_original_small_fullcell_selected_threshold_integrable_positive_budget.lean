-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a361_original_small_fullcell_selected_threshold_integrable_positive_budget
-- name    : AvramDividend.Classical.avram_ga_a361_original_small_fullcell_selected_threshold_integrable_positive_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:02:27.750185+00:00
-- url     : https://prove2.me/theorems/2a143a7b-3be8-4d3c-984e-dbc7970ab1a0
-- title:
--   True original stopped Gaussian combined small-cell source admits a threshold with integrable eventually arbitrarily small positive expected budget
-- statement:
--   For each positive tolerance η on the genuine original Gaussian full stopped physical mesh, some positive small raw-increment cutoff δ has two properties simultaneously: the corresponding positive small-cell source is integrable for every finite mesh, and after some level its expected positive contribution is at most η. This is the minimal sufficient small-source obligation for closing original a216 using the proved genuine large-cell branch a263, exact partition a266, aestrong measurability a267 and generic selected-threshold gluing a360. It strictly weakens the stronger all-threshold integrability source a264.
-- source:
--   Avram top-cap original a216 genuine Gaussian physical stopped full-cell small positive source; a194/a240/a236/a150 and positive mesh regularisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a361_original_small_fullcell_selected_threshold_integrable_positive_budget
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
    let Small : ℝ → ℕ → Ω → ℝ := fun δ m ω =>
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
      if s i < ρ ω ∧ s i + Δ ≤ ρ ω ∧ |R i| < δ then F i else 0
    ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧
        (∀ m, Integrable (fun ω => max (Small δ m ω) 0) P) ∧
        ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
          (∫ ω, max (Small δ m ω) 0 ∂P) ≤ η := by sorry
