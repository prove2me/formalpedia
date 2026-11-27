-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_uniform_grid_properties
-- name    : AvramDividend.Classical.avram_locmoll_band_uniform_grid_properties
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:15:59.795223+00:00
-- url     : https://prove2.me/theorems/dbcdef74-0cf9-4c94-813c-34f53330b671
-- title:
--   Uniform normalised grids are monotone and reach the exact bounded horizon
-- statement:
--   Uniform normalised grids are monotone and reach the exact bounded horizon
-- source:
--   Exact physical grid decomposition of 11f1a409-adc5-538d-b8b2-be83efcb307e using 2983886e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_band_uniform_grid_properties
    (H : ℝ≥0) (m : ℕ → ℕ) :
    let u : ℕ → ℕ → ℝ≥0 := fun n i => (i : ℝ≥0) * H / ((m n : ℝ≥0) + 1)
    let k : ℕ → ℕ := fun n => m n + 1
    (∀ n, Monotone (u n)) ∧ (∀ n, u n 0 = 0) ∧ (∀ n, u n (k n) = H) := by sorry
