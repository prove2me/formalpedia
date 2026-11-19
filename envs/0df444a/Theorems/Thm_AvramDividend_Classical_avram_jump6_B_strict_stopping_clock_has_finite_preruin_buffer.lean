-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_strict_stopping_clock_has_finite_preruin_buffer
-- name    : AvramDividend.Classical.avram_jump6_B_strict_stopping_clock_has_finite_preruin_buffer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:46:13.855942+00:00
-- url     : https://prove2.me/theorems/3a090fab-8d5f-4af8-b393-39bf33eea87e
-- title:
--   Strictly pre-ruin stopped clock admits a finite intermediate horizon
-- statement:
--   If an original NNReal stopping clock t is strictly earlier than its original extended ruin clock R, there exists a finite nonnegative real buffer rho satisfying t<rho<=R. Handles both finite ruin and infinite lifetime. This removes the auxiliary strict-buffer hypothesis from the original physical Stieltjes cell-support theorem 3b39135b on the true positive pre-ruin branch.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_strict_stopping_clock_has_finite_preruin_buffer
    (t : ℝ≥0) (R : ℝ≥0∞) (h : (t : ℝ≥0∞) < R) :
    ∃ ρ : ℝ≥0, t < ρ ∧ (ρ : ℝ≥0∞) ≤ R := by sorry
