-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_grid_step_small_of_16000_times_n_le
-- name    : AvramDividend.Classical.avram_gaussianB_grid_step_small_of_16000_times_n_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T21:42:59.840337+00:00
-- url     : https://prove2.me/theorems/d308b759-b507-4d0e-b40b-b7e62bbb8ead
-- title:
--   Original physical Gaussian grid step at most 1/16000 when m+1 is at least 16000n
-- statement:
--   For the original physical mesh Δ_m=n/(m+1), the explicit natural refinement m+1≥16000n ensures Δ_m≤1/16000. This is exactly the extension allowed by the Proved unconditional canonical Gaussian centred-source joint tube through 17/16000, beyond the fixed T=1/1000 stopped horizon.

import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_grid_step_small_of_16000_times_n_le
    (n m : ℕ) (hm : 16000 * n ≤ m + 1) :
    (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0) ≤ (1 / 16000 : ℝ≥0) := by sorry
