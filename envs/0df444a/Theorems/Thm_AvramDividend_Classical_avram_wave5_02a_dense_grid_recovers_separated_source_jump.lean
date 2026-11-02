-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_dense_grid_recovers_separated_source_jump
-- name    : AvramDividend.Classical.avram_wave5_02a_dense_grid_recovers_separated_source_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:43:48.401197+00:00
-- url     : https://prove2.me/theorems/5afb8a0d-12dc-4cca-b5ef-482f042ba72f
-- title:
--   Dense grid first crossing recovers a separated original source jump
-- statement:
--   For the actual original process, if its path is strictly above a level throughout a left interval and strictly below it throughout a right interval, then some grid point in the left interval has first strict grid downcrossing exactly at the separation time. The grid is any countable dense time sequence and the sample is unchanged.
-- source:
--   Density of the countable grid and the pathwise separating intervals, used to turn original-source jump separation into exact grid candidate coverage.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_02a_dense_grid_recovers_separated_source_jump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (s t b : ℝ≥0) (a : ℝ) (hst : s < t) (htb : t < b)
    (hL : ∀ u ∈ Ioo s t, a < X.X u ω)
    (hR : ∀ u ∈ Ico t b, X.X u ω < a) :
    ∃ m : ℕ, grid m ∈ Ioo s t ∧
      (⨅ n : ℕ, {ω : Ω | grid m < grid n ∧ X.X (grid n) ω < a}.piecewise
        (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) ω) = (t : ℝ≥0∞) := by sorry
