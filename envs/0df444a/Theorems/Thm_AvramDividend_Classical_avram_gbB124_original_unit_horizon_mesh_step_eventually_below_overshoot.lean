-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB124_original_unit_horizon_mesh_step_eventually_below_overshoot
-- name    : AvramDividend.Classical.avram_gbB124_original_unit_horizon_mesh_step_eventually_below_overshoot
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:28:23.099921+00:00
-- url     : https://prove2.me/theorems/2a16c875-5573-416a-8882-3c8bd49713aa
-- title:
--   Original physical grid step is below the extra Brownian tube horizon for sufficiently fine meshes
-- statement:
--   For original unit-horizon physical mesh Delta_m=1/(m+1), any m at least 15999 has Delta_m at most 1/16000. Hence all stopped finite-grid cells ending after the short stopping time T=1/1000 remain within the longer horizon T+1/16000 of the Proved B106 positive Brownian tube. This bridges source-tube support to the exact numerical mesh parameters.

import Mathlib
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB124_original_unit_horizon_mesh_step_eventually_below_overshoot
    (m : ℕ) (hm : 15999 ≤ m) :
    (1 : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0) ≤
      (1 / 16000 : ℝ≥0) := by sorry
