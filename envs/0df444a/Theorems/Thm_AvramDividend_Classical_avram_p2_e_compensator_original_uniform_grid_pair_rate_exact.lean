-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_uniform_grid_pair_rate_exact
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_uniform_grid_pair_rate_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:08:09.891901+00:00
-- url     : https://prove2.me/theorems/6e416dba-79ef-4340-b400-f9cc75475b8e
-- title:
--   Exact original marked-jump past-future rectangular expectation on physical uniform grid
-- statement:
--   The exact source original-process finite-grid past-future negative-band marked-count product expectation equals its rectangular Lévy rate sum on the physical uniform grid of k+1 half-open cells.
-- source:
--   Accepted exact original finite-grid rate theorem 77b37394 specialised with the source-compatible uniform_grid_cell_bounds helper. Preserves the literal original Lévy jump process and clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_grid_pair_rate_sum_exact
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_uniform_grid_cell_bounds

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p2_e_compensator_original_uniform_grid_pair_rate_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (k n : ℕ) :
    let s : Fin (k + 1) → ℝ≥0 := fun i =>
      (i.val : ℝ≥0) * (T / ((k : ℝ≥0) + 1))
    let t : Fin (k + 1) → ℝ≥0 := fun i =>
      (((i.val + 1 : ℕ) : ℝ≥0) * (T / ((k : ℝ≥0) + 1)))
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    (∫⁻ ω, ∑ i : Fin (k + 1), N 0 (s i) ω * N (s i) (t i) ω ∂P) =
      ∑ i : Fin (k + 1), ((s i : ℝ≥0∞) * X.ν B) *
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν B) := by sorry
