-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a45_original_uniform_clipped_source_active_cell_envelope
-- name    : AvramDividend.Classical.avram_ga_a45_original_uniform_clipped_source_active_cell_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T15:54:49.001204+00:00
-- url     : https://prove2.me/theorems/077437f8-e642-43a2-bc80-0a76008650de
-- title:
--   Mesh-independent original clipped Gaussian cell exponential envelope
-- statement:
--   For the original Gaussian spectrally negative Levy process and admissible dividend strategy at a finite clipped horizon, there are fixed nonnegative theta, K and b chosen once from physical HJB exponential growth and compact reserve band. Every mesh order obeys the same lower value and upper exponential active-cell bounds, with zero inactive cells. Extract the exact accepted gledger72 proof by moving the mesh introduction after choosing its constants.
-- source:
--   Exact accepted gledger72 proof bbaf2c1d; Proved gledger63, gledger65, and original a41b.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_strict_prefix_postpayment_floor
import Theorems.Thm_AvramDividend_Classical_avram_gledger54_original_stopped_source_cell_prepayment_floor
import Theorems.Thm_AvramDividend_Classical_avram_gledger63_compact_continuous_value_finite_lower_bound
import Theorems.Thm_AvramDividend_Classical_avram_gledger65_original_topcap_HJB_positive_halfline_exponential_upper
import Theorems.Thm_AvramDividend_Classical_avram_gledger70_original_stopped_source_inactive_cell_zero
import Theorems.Thm_AvramDividend_Classical_riskProcess_tendsto_postPaymentReserve_right
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Active physical cells carry a compact postpayment lower band and an
    exponential prepayment upper bound; inactive cells contribute zero. -/

theorem AvramDividend.Classical.avram_ga_a45_original_uniform_clipped_source_active_cell_envelope
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
    ∃ θ K b : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧ 0 ≤ b ∧
    ∀ m : ℕ,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → Ω → ℝ≥0 := fun i ω => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℕ → Ω → ℝ := fun i ω => Real.exp (-(q * (v i ω : ℝ)))
      let Y : ℕ → Ω → ℝ := fun i ω =>
        x + X.X (v i ω) ω - rightLimit D (v i ω) ω
      let Z : ℕ → Ω → ℝ := fun i ω =>
        x + X.X (v (i + 1) ω) ω - rightLimit D (v i ω) ω
      let S : Ω → ℝ := fun ω => Finset.sum (Finset.range (m + 1)) (fun i =>
        (E (i + 1) ω - E i ω) * w (Y i ω) +
        E (i + 1) ω * (w (Z i ω) - w (Y i ω)))
      (∀ᵐ ω ∂P, ∀ i ∈ Finset.range (m + 1),
          (E (i + 1) ω = E i ω ∧ Z i ω = Y i ω) ∨
          (-b ≤ w (Y i ω) ∧
            w (Z i ω) ≤ K * Real.exp (θ * Z i ω))) := by sorry
