-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a160_original_gaussian_mcell_clipped_spatial_value_aestrongly_measurable
-- name    : AvramDividend.Classical.avram_ga_a160_original_gaussian_mcell_clipped_spatial_value_aestrongly_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T13:02:03.110214+00:00
-- url     : https://prove2.me/theorems/fce58847-1aa3-4706-9446-25f9ec7c3c23
-- title:
--   Exact original stopped Gaussian m-cell positive-domain discounted spatial value sum is a.e. strongly measurable
-- statement:
--   For the actual original spectrally negative zero-jump Gaussian Lévy process and admissible dividend right limit D, under the existing top-cap positive reserve C2 assumptions, the discounted m-cell stopped spatial value sum in the b0 root is a.e. strongly measurable at each physical mesh order. The source observations ga43 give each measurable E,Y,Z and the finite active-cell alternative (equal endpoints or both positive); ga158 identifies the original smooth positive domain, and ga159 transfers to the exact finite spatial sum without requiring value w to be measurable on negative reserves.
-- source:
--   Proved original clipped Gaussian source observations ga43; positive halfline continuity ga158 and finite-index measured spatial values ga159, requiring child proofs before publication.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a43_original_clipped_spatial_cell_observations
import Theorems.Thm_AvramDividend_Classical_avram_ga_a158_original_topcap_C2_value_continuous_positive_halfline
import Theorems.Thm_AvramDividend_Classical_avram_ga_a159_original_gaussian_finite_active_positive_domain_spatial_sum_measurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a160_original_gaussian_mcell_clipped_spatial_value_aestrongly_measurable
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
    (hρle : ∀ ω, ρ ω ≤ τ ω)
    (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let S : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → Ω → ℝ≥0 := fun i ω => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℕ → Ω → ℝ := fun i ω => Real.exp (-(q * (v i ω : ℝ)))
      let Y : ℕ → Ω → ℝ := fun i ω => x + X.X (v i ω) ω - rightLimit D (v i ω) ω
      let Z : ℕ → Ω → ℝ := fun i ω =>
        x + X.X (v (i + 1) ω) ω - rightLimit D (v i ω) ω
      ∑ i ∈ Finset.range m, E (i + 1) ω * (w (Z i ω) - w (Y i ω))
    ∀ m, AEStronglyMeasurable (S m) P := by sorry
