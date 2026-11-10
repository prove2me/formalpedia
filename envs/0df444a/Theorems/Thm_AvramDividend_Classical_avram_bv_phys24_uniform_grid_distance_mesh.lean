-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_phys24_uniform_grid_distance_mesh
-- name    : AvramDividend.Classical.avram_bv_phys24_uniform_grid_distance_mesh
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T22:28:11.1101+00:00
-- url     : https://prove2.me/theorems/e9663d02-3ba1-465d-a495-47d3272a3949
-- title:
--   Actual original BV uniform physical grid has distance mesh tending to zero
-- statement:
--   For the exact positive-width physical grid prescribed in the corrected finite-cap Avram theorem, every real-distance cell width tends to zero uniformly in the cell index. The proof reuses the accepted exact-width and delta-profile lemmas.
-- source:
--   Directly supplies the source-exact mesh premise of Proved 5ca01b4f, necessary to control finite-activity multiple-jump collisions in child 8e6c1861 of e6a0b83b.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_phys24_uniform_grid_distance_mesh
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in (atTop : Filter ℕ), ∀ i : ℕ, i < n + 1 →
        dist (u n i) (u n (i + 1)) < ε := by sorry
