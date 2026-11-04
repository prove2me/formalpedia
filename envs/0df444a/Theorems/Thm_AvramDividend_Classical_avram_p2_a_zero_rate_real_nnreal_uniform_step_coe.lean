-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_real_nnreal_uniform_step_coe
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_real_nnreal_uniform_step_coe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:12:53.660553+00:00
-- url     : https://prove2.me/theorems/afd5a3e4-3adb-48b3-ae31-d1f38cf666b2
-- title:
--   Real and nonnegative-real original uniform mesh widths coincide
-- statement:
--   Identify exactly the mesh conventions in the accepted P2-A original-path grid and the independent P2-J expectation convergence theorem: Real.toNNReal ((T:Real)/(n+1)) equals T/(n+1) computed in NNReal for any nonnegative horizon. Prove by coercion to real and positivity. This enables a source-exact expectation-pathwise bridge with no discretisation approximation.

import Mathlib.Data.NNReal.Defs
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_real_nnreal_uniform_step_coe
    (T : ℝ≥0) (n : ℕ) :
    Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1)) =
      T / ((n : ℝ≥0) + 1) := by sorry
