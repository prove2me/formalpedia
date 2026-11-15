-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a263_original_combined_fullcell_large_raw_increment_positive_L1
-- name    : AvramDividend.Classical.avram_ga_a263_original_combined_fullcell_large_raw_increment_positive_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:53:27.542311+00:00
-- url     : https://prove2.me/theorems/583d7c20-669a-4d8a-b073-f6145e13efb7
-- title:
--   True stopped original Gaussian combined fullcell large-raw-increment positive residual vanishes expected L1
-- statement:
--   For the identical original Gaussian topcap HJB source and physical stopped full-cell mesh as a216, restrict each cell to the large raw Gaussian increment event δ≤|R| with arbitrary δ>0. The positive part of this true combined discounted Taylor/Hessian residual is integrable and has vanishing expectation as the physical mesh refines. The proof uses the global positive endpoint HJB envelope a257/a259, large-cell source majorant a258/a260, rare polynomial-to-raw-square domination a261, original fullcell raw-large-square a187 and positive exponential a233. Complements the small-increment source branch to close a216 without the unreliable isolated discount-positive a151.
-- source:
--   Original source a216 exact theorem statement plus large mask δ≤|R|; source a187/a233/a258/a260/a261

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a263_original_combined_fullcell_large_raw_increment_positive_L1
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
    let Large : ℕ → Ω → ℝ := fun m ω =>
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
    (∀ m, Integrable (fun ω => max (Large m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (Large m ω) 0 ∂P) atTop (nhds (0 : ℝ)) := by sorry
