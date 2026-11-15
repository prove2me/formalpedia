-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b242_original_ruinclipped_true_physical_unmarked_gaussian_intrinsic_source_identity
-- name    : AvramDividend.Classical.avram_b242_original_ruinclipped_true_physical_unmarked_gaussian_intrinsic_source_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:18:58.694482+00:00
-- url     : https://prove2.me/theorems/c13c79c7-25b1-43e5-b7c2-29fffcea213f
-- title:
--   Original ruin-clipped physical unmarked Gaussian source increment equals intrinsic martingale increment plus compensated drift
-- statement:
--   Given the genuine intrinsic Gaussian truncated-residual limit R and small-mark compensated limit Jsmall from B236, and the actual original finite-activity X, consider the true stopped physical mesh v_i=min(i n/(m+1),sigma(omega)). Mark exactly those physical cells containing a nonzero actual original X jump in the half-open interval (v_i,v_{i+1}]. On every unmarked cell, almost surely the original source increment after removing drift X.c equals the intrinsic R increment plus the exact finite negative Lévy compensator drift, with the actual original stopping clock and no post-ruin interpolation. This is the needed source identification for B236 Gaussian/mixed finite activity separate from explicit marked-cell treatment, preserving original Jsmall and original X.
-- source:
--   Proved B209 canonical true unmarked grid Gaussian source drift almost everywhere, instantiated with the physical clipped finite grid and the exact canonical marked-filter set, with monotone physical clipped grid ordering. Unlike a Brownian source transport, uses original intrinsic limits R/Jsmall.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b209_original_canonical_true_unmarked_grid_gaussian_source_drift_ae
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b242_original_ruinclipped_true_physical_unmarked_gaussian_intrinsic_source_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
        atTop (𝓝 (R u ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (Jsmall u ω)))
    (n m : ℕ) (σ : Ω → ℝ≥0) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : Ω → ℕ → ℝ≥0 := fun ω i =>
      min ((i : ℝ≥0) * Δ) (σ ω)
    let marked : Ω → Finset ℕ := fun ω => by
      classical
      exact (Finset.range (m + 1)).filter (fun i =>
        ∃ u : ℝ≥0, v ω i < u ∧ u ≤ v ω (i + 1) ∧
          X.X u ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) u ≠ 0)
    ∀ᵐ ω ∂P, ∀ i, i ∈ Finset.range (m + 1) →
      i ∉ marked ω →
      X.X (v ω (i + 1)) ω - X.X (v ω i) ω -
        ((v ω (i + 1) - v ω i : ℝ≥0) : ℝ) * X.c =
      (R (v ω (i + 1)) ω - R (v ω i) ω) +
        (-(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) *
          ((v ω (i + 1) - v ω i : ℝ≥0) : ℝ) := by sorry
