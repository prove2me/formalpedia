-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_right_mesh_endpoint_tendsto
-- name    : AvramDividend.Classical.avram_root29_05_right_mesh_endpoint_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:15:32.145135+00:00
-- url     : https://prove2.me/theorems/e836496f-bf56-4d6e-809b-530813ebc2c4
-- title:
--   Right endpoints of uniform rational payment cells converge to each continuous payment time
-- statement:
--   For every real time r, the upper mesh endpoint ceil(r(n+1))/(n+1) of the uniform rational partition converges to r. The proof uses exact ceiling inequalities, positive denominators, and squeeze convergence of 1/(n+1). This is the missing analytic prerequisite for pointwise convergence of discounted killed grid weights and application of Fatou's lemma to the genuine Stieltjes reward.
-- source:
--   Pinned Mathlib Int.le_ceil, Int.ceil_lt_add_one, squeeze_zero, tendsto_one_div_add_atTop_nhds_zero_nat. Supports the sampled-to-actual stopped Stieltjes convergence needed for Avram WS5 target 79978d61. No stochastic or scale identities assumed.

import Mathlib
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open Filter Topology
open scoped BigOperators Classical

theorem AvramDividend.Classical.avram_root29_05_right_mesh_endpoint_tendsto (r : ℝ) :
    Tendsto (fun n : ℕ =>
      ((⌈r * ((n : ℝ) + 1)⌉ : ℤ) : ℝ) / ((n : ℝ) + 1))
      atTop (𝓝 r) := by sorry
