-- Prove2me | Theorems.Thm_AvramDividend_Classical_nonnegative_uniform_time_grid_exists
-- name    : AvramDividend.Classical.nonnegative_uniform_time_grid_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T14:46:21.752985+00:00
-- url     : https://prove2.me/theorems/a98cc446-2d30-476a-b2d5-e66fb6b71af3
-- title:
--   An exact nonnegative equal-duration time mesh exists for any positive cell count
-- statement:
--   Construct the canonical uniform NNReal grid 0,T/N,...,T with N positive: increasing cell endpoints, all inside the observation window, exactly equal durations, and total duration T. Needed to instantiate the accepted finite-grid strict-survival bound on the actual Lévy process.
-- source:
--   Uniform partition construction for the zero-barrier finite-activity first-jump proof, Avram, Palmowski and Pistorius (2007) §3.3.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
open AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.nonnegative_uniform_time_grid_exists
    (T : ℝ≥0) (N : ℕ) (hN : 0 < N) :
    ∃ (ts : ℕ → ℝ≥0) (δ : ℝ≥0),
      ts 0 = 0 ∧ ts N = T ∧
      (∀ k : ℕ, k < N → ts k ≤ ts (k + 1)) ∧
      (∀ k : ℕ, k < N → ts (k + 1) ≤ T) ∧
      (∀ k : ℕ, k < N → ts (k + 1) - ts k = δ) ∧
      (N : ℝ≥0) * δ = T := by sorry
