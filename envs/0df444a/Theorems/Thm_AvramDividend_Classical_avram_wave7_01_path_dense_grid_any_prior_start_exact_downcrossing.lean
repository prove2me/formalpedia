-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_path_dense_grid_any_prior_start_exact_downcrossing
-- name    : AvramDividend.Classical.avram_wave7_01_path_dense_grid_any_prior_start_exact_downcrossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:51:45.672535+00:00
-- url     : https://prove2.me/theorems/d31caf75-7535-4701-9a1c-4f63ae0cbd5b
-- title:
--   Every grid start preceding a locally separated negative jump yields its exact first-downcrossing time
-- statement:
--   For a real path with a strict downward threshold separation around t, every dense-grid starting point strictly between s and t has its first future rational-grid threshold downcrossing infimum exactly at t. The result is stronger than existence of one such starting point, removes a choice from the first-hit selector proof and is independent of any stochastic model.
-- source:
--   Direct dense-grid sandwich of the first-downcrossing extended infimum using open left/right neighbourhood separation; the original-source Proved 5afb8a0d supplies the known analytic pattern.

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave7_01_path_dense_grid_any_prior_start_exact_downcrossing
    (Y : ℝ≥0 → ℝ)
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (s t b : ℝ≥0) (a : ℝ) (hst : s < t) (htb : t < b)
    (hL : ∀ u ∈ Ioo s t, a < Y u)
    (hR : ∀ u ∈ Ico t b, Y u < a) :
    ∀ m : ℕ, grid m ∈ Ioo s t →
      (⨅ n : ℕ,
        {Z : ℝ≥0 → ℝ | grid m < grid n ∧ Z (grid n) < a}.piecewise
          (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) Y) =
      (t : ℝ≥0∞) := by sorry
