-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a163_original_full_mesh_source_endpoint_positive
-- name    : AvramDividend.Classical.avram_ga_a163_original_full_mesh_source_endpoint_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:26:54.901181+00:00
-- url     : https://prove2.me/theorems/d23e6c6d-6e4c-49c1-9cf1-80c89cadbac9
-- title:
--   Original zero-jump Gaussian physically full pre-stop mesh cell has positive source spatial endpoints almost surely
-- statement:
--   For the original zero-jump spectrally negative Gaussian Levy source and dividend strategy, on each physical mesh any cell completely before the original stopping clock has strictly positive post-payment source reserve at its initial time and strictly positive pre-payment reserve at its endpoint, almost surely. Includes the endpoint s+delta=stop using Proved ga43, rather than assuming strict inequality.
-- source:
--   Existing original stopped ga43 positive endpoint disjunction plus gledger137 actual postpayment compact prefix band; exact original X.X and rightLimit D.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a43_original_clipped_spatial_cell_observations
import Theorems.Thm_AvramDividend_Classical_avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a163_original_full_mesh_source_endpoint_positive
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
    ∀ m : ℕ, ∀ᵐ ω ∂P, ∀ i ∈ Finset.range m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      (s < ρ ω ∧ s + Δ ≤ ρ ω) →
      0 < x + X.X s ω - rightLimit D s ω ∧
      0 < x + X.X s ω - rightLimit D s ω +
        (X.X (s + Δ) ω - X.X s ω) := by sorry
