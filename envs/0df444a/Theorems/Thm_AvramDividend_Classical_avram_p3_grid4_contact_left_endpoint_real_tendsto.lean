-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_contact_left_endpoint_real_tendsto
-- name    : AvramDividend.Classical.avram_p3_grid4_contact_left_endpoint_real_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:50:45.55277+00:00
-- url     : https://prove2.me/theorems/09818bfd-683f-489f-9f64-f6dc15488afa
-- title:
--   Original physical contact-tail truncated left endpoints converge to their stopped clock
-- statement:
--   For any nonnegative stopped clock tau and physical positive horizon T, the actual truncated-subtraction left endpoints (tau - T/(n+1)) coerced to real converge to tau. This uses the proved source uniform NNReal mesh width limit b554b287, NNReal.coe_sub_def, continuity of real subtraction and max. It supplies the missing endpoint-convergence hypothesis for the source-faithful BV-ENV3 closed/strict crossing-cell cash limit theorems.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_nnreal_width_tendsto_zero
open Filter Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p3_grid4_contact_left_endpoint_real_tendsto
    (τ T : ℝ≥0) :
    Tendsto (fun n : ℕ =>
      ((τ - T / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ))
      atTop (𝓝 (τ : ℝ)) := by sorry
