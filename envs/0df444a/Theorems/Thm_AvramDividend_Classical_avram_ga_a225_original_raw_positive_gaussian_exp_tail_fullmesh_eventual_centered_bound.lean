-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a225_original_raw_positive_gaussian_exp_tail_fullmesh_eventual_centered_bound
-- name    : AvramDividend.Classical.avram_ga_a225_original_raw_positive_gaussian_exp_tail_fullmesh_eventual_centered_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T07:48:33.365261+00:00
-- url     : https://prove2.me/theorems/37c43629-0ede-46e4-8671-6802d1ed0000
-- title:
--   Original Gaussian physical full-grid raw positive exponential large-cell tail eventually bounded by centred Gaussian positive tails
-- statement:
--   For the original Gaussian Lévy source and the exact finite-horizon physical grid, once the deterministic source drift becomes small relative to a positive raw threshold, every actual raw positive large-increment exponential tail is bounded pointwise by a fixed exp(theta delta/2) multiple of the corresponding centred normalised Gaussian positive tail. The result is uniform across every finite physical mesh cell and sample path, and feeds the true combined-source a216.
-- source:
--   Original exact physical mesh drift a223 and positive raw-to-centered Gaussian Chernoff a222, source exact X.X

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a222_raw_positive_Gaussian_exponential_tail_dominated_by_centered_normalised
import Theorems.Thm_AvramDividend_Classical_avram_ga_a223_original_physical_gaussian_drift_below_half_tail_threshold_eventually
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a225_original_raw_positive_gaussian_exp_tail_fullmesh_eventual_centered_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : 0 < X.σ) (n : ℕ) (θ δ : ℝ)
    (hθ : 0 ≤ θ) (hδ : 0 < δ) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
    let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X (s m i + Δ m) ω - X.X (s m i) ω
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      (R m i ω - (Δ m : ℝ) * X.c) / X.σ
    ∀ᶠ m : ℕ in atTop, ∀ ω : Ω,
      (∑ i ∈ Finset.range m,
        if δ ≤ R m i ω then Real.exp (θ * R m i ω) else 0) ≤
      Real.exp (θ * δ / 2) *
      (∑ i ∈ Finset.range m,
        if δ / (2 * X.σ) ≤ Z m i ω
        then Real.exp ((θ * X.σ) * Z m i ω) else 0) := by sorry
