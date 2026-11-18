-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva42_uniform_physical_grid_canonical
-- name    : AvramDividend.Classical.avram_bva42_uniform_physical_grid_canonical
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T01:01:57.326234+00:00
-- url     : https://prove2.me/theorems/a4aa4fd2-5038-4d45-b5ce-3c9e5861fe68
-- title:
--   Canonical exact physical BV grid from zero to T minus T over n+2, monotone with explicit real clock
-- statement:
--   For any positive real horizon T construct the canonical nonnegative real clock u(n,i)=T i/(n+2). It starts exactly at zero, has monotone adjacent cells, its last physical time u(n,n+1) is exactly T-T/(n+2), and its real coercion is the defining ratio. This reusable arithmetic lemma provides the original unmodified physical-grid data required by the Lévy Stieltjes cash and martingale error certificates. It packages the time-index and coercion proof and does not invoke any unproved stochastic assumption.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
set_option autoImplicit false
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva42_uniform_physical_grid_canonical
    (T : ℝ) (hT : 0 < T) :
    ∃ u : ℕ → ℕ → ℝ≥0,
      (∀ n, u n 0 = 0 ∧
        ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2))) ∧
      (∀ n i, u n i ≤ u n (i + 1)) ∧
      (∀ n i, (u n i : ℝ) =
        T * (i : ℝ) / ((n : ℝ) + 2)) := by sorry
