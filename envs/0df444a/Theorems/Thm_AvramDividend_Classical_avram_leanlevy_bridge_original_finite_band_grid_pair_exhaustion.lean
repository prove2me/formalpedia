-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_finite_band_grid_pair_exhaustion
-- name    : AvramDividend.Classical.avram_leanlevy_bridge_original_finite_band_grid_pair_exhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:04:50.727622+00:00
-- url     : https://prove2.me/theorems/9125f6f8-d31e-40b4-b092-d78ecc139121
-- title:
--   Original finite negative-band chronological pairs are eventually exhausted by increasing grids
-- statement:
--   For the literal finite set of negative-band jump times on one path of Avram's original X, any increasing family of grid-detected chronological pairs which lies inside, and eventually covers, every actual ordered pair becomes exactly equal to the entire physical ordered-pair set at a finite level. This discharges the finite-path combinatorial stabilisation step in the original second-factorial-moment passage; the separate physical grid coverage and integrability calculations remain genuine obligations.
-- source:
--   Original finite-jump-times theorem and Proved P2-E grid-pair mean 77b37394, cross-window mean a8adacce, open full chronological pair theorem d938e9a5; finite set induction with a maximum grid threshold.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_leanlevy_bridge_original_finite_band_grid_pair_exhaustion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ)
    (F : Finset ℝ≥0)
    (hF : F = (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset)
    (G : ℕ → Finset (ℝ≥0 × ℝ≥0))
    (hSub : ∀ m, G m ⊆ (F ×ˢ F).filter (fun p => p.1 < p.2))
    (hMono : Monotone G)
    (hCover : ∀ p ∈ (F ×ˢ F).filter (fun p => p.1 < p.2),
      ∃ m, p ∈ G m) :
    ∃ N, ∀ m ≥ N, G m = (F ×ˢ F).filter (fun p => p.1 < p.2) := by sorry
