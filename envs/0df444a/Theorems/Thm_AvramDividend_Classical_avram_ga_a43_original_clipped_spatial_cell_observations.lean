-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a43_original_clipped_spatial_cell_observations
-- name    : AvramDividend.Classical.avram_ga_a43_original_clipped_spatial_cell_observations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T13:07:24.892639+00:00
-- url     : https://prove2.me/theorems/df216983-f2cc-4e4f-be33-30740ed91737
-- title:
--   Original clipped Gaussian grid measurable states and positive active-cell alternative
-- statement:
--   The original clipped Gaussian grid has measurable discount, prepayment reserve and postpayment source observations and almost every cell is inactive with identical source states or active with both states strictly positive. Exact intermediate facts extracted from the existing Proved gledger71 proof, for use in a42 and the original terminal spatial-cell measurability a41a. No auxiliary source.
-- source:
--   Accepted proof 48e93291-27ac-4940-97f2-dab9a19d966c from gledger71 6b3d4114.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_strict_prefix_postpayment_floor
import Theorems.Thm_AvramDividend_Classical_avram_gledger54_original_stopped_source_cell_prepayment_floor
import Theorems.Thm_AvramDividend_Classical_avram_gledger67_original_clipped_gaussian_mesh_stops_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gledger70_original_stopped_source_inactive_cell_zero
import Theorems.Thm_AvramDividend_Classical_avram_gledger74_measurable_original_clipped_NNReal_clock_to_real
import Theorems.Thm_AvramDividend_Classical_avram_gledger75_original_stopped_levy_and_rightDividend_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gledger76_positive_only_value_masked_physical_source_measurable
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option maxHeartbeats 800000

theorem AvramDividend.Classical.avram_ga_a43_original_clipped_spatial_cell_observations
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
    ∀ m : ℕ,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → Ω → ℝ≥0 := fun i ω => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℕ → Ω → ℝ := fun i ω => Real.exp (-(q * (v i ω : ℝ)))
      let Y : ℕ → Ω → ℝ := fun i ω =>
        x + X.X (v i ω) ω - rightLimit D (v i ω) ω
      let Z : ℕ → Ω → ℝ := fun i ω =>
        x + X.X (v (i + 1) ω) ω - rightLimit D (v i ω) ω
      (∀ i : ℕ, Measurable (E i)) ∧
      (∀ i : ℕ, Measurable (Y i)) ∧
      (∀ i : ℕ, Measurable (Z i)) ∧
      (∀ᵐ ω ∂P, ∀ i ∈ Finset.range (m + 1),
        (E (i + 1) ω = E i ω ∧ Z i ω = Y i ω) ∨
        (0 < Y i ω ∧ 0 < Z i ω)) := by sorry
