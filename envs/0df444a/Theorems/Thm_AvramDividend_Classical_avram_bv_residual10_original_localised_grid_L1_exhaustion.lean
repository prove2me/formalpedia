-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_localised_grid_L1_exhaustion
-- name    : AvramDividend.Classical.avram_bv_residual10_original_localised_grid_L1_exhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T14:16:40.48118+00:00
-- url     : https://prove2.me/theorems/2aef8d53-7ef0-4bba-b89a-e4f102ac1f6f
-- title:
--   Original BV residual grids have measurable exhaustive integrable compact-coordinate localisations
-- statement:
--   For a fixed original bounded-variation spectrally negative Levy physical grid and each coordinatewise measurable path-dependent coefficient, there exists an explicit sequence of measurable coefficient-bound events. Every sample path belongs to all sufficiently high levels, and the true untruncated original real-jump-tsum residual mesh restricted to each level is integrable. This combines separately proved coordinate-event measurability, exhaustion, and original-process compact-event integrability. It does not claim uniform integrability of the localised sums or global original source integrability.
-- source:
--   AVRAM BV-RESIDUAL10 exact original uniform-grid stochastic integration compact-exhaustion bridge, 7 November 2026

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_event_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_compact_localised_R_mesh_L1

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_localised_grid_L1_exhaustion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (T : ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hu : ∀ i, i < n + 1 → u n i ≤ u n (i + 1))
    (hu0 : u n 0 = 0) (huT : u n (n + 1) ≤ T)
    (a : Ω → ℕ → ℝ) (ha : ∀ i, Measurable (fun ω => a ω i)) :
    ∃ A : ℕ → Set Ω,
      (∀ k, MeasurableSet (A k)) ∧
      (∀ ω, ∀ᶠ k in atTop, ω ∈ A k) ∧
      (∀ k, Integrable (fun ω =>
        if ω ∈ A k then
          let J : ℝ≥0 → ℝ := fun t =>
            ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
          let R : ℝ≥0 → ℝ := fun t =>
            ((t : ℝ) * X.drift - X.X t ω) - J t
          ∑ i ∈ Finset.range (n + 1),
            a ω i * (R (u n i) - R (u n (i + 1)))
        else 0) P) := by sorry
