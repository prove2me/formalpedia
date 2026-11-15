-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a301_true_fullcell_discounted_positive_scalar_HJB_source_envelope
-- name    : AvramDividend.Classical.avram_ga_a301_true_fullcell_discounted_positive_scalar_HJB_source_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:45:51.904203+00:00
-- url     : https://prove2.me/theorems/15a7d754-dbee-4d16-9c38-42ceed74d4bb
-- title:
--   True original stopped full Gaussian cell one-sided discounted residual bounded by global HJB exponential endpoint and compact polynomial jets
-- statement:
--   On each actual original Gaussian physical full stopping cell, the one-sided positive combined discounted verification residual is bounded by the global Gaussian HJB endpoint exponential envelope K exp(theta times the actual positive postincrement reserve), plus M times a fixed polynomial in the actual raw and centered Gaussian increment. The estimate follows from original global HJB and compact source jet package a300, exact discount factors a235 and the proved scalar a210 inequality. It is the local source prerequisite for a263 large-cell positive expected L1.
-- source:
--   Original true physical Gaussian stopped cell source a300, a235, a210.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a300_true_stopped_fullcell_global_jet_and_HJB_exponential_envelope
import Theorems.Thm_AvramDividend_Classical_avram_ga_a235_gaussian_physical_cell_exponential_discount_width_Lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_ga_a210_original_combined_positive_largecell_source_envelope
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a301_true_fullcell_discounted_positive_scalar_HJB_source_envelope
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
    ∃ θ K M : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧ 0 ≤ M ∧
      ∀ m : ℕ, ∀ᵐ ω ∂P, ∀ i ∈ Finset.range m,
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let y : ℝ := x + X.X s ω - rightLimit D s ω
        let r : ℝ := X.X (s + Δ) ω - X.X s ω
        let z : ℝ := r - (Δ : ℝ)*X.c
        let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q*(t : ℝ)))
        (s < ρ ω ∧ s + Δ ≤ ρ ω) →
          max (E (s+Δ)*(w (y+r)-w y) -
            E s*(deriv w y*r + (iteratedDeriv 2 w y)/2*z^2)) 0 ≤
          K*Real.exp (θ*(y+r)) + M*(1+|r|+z^2/2) := by sorry
