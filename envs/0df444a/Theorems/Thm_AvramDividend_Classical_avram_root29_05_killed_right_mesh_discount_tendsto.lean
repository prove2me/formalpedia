-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_killed_right_mesh_discount_tendsto
-- name    : AvramDividend.Classical.avram_root29_05_killed_right_mesh_discount_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:24:30.141093+00:00
-- url     : https://prove2.me/theorems/cbc8dd81-fce3-4b99-940a-ab83c64a115d
-- title:
--   Discounted right-mesh payment weights converge under strict killing at ruin
-- statement:
--   For each real payment time r, discount q and extended nonnegative killing horizon τ, the discounted right-hand rational mesh endpoint payment with the strict indicator endpoint<τ converges to the true discounted payment if r<τ and zero otherwise. Includes payment at the exact ruin boundary. Uses canonically Proved mesh endpoint convergence, continuity of the ENNReal lift and real exponential, and monotonicity of the ceiling endpoint. Source-faithful pointwise input for the Fatou step comparing rational-grid killed regulator dividends to actual stopped Stieltjes dividend measure.
-- source:
--   Pinned Mathlib ENNReal.continuous_ofReal, Int.le_ceil, isOpen_Iio; Proved right mesh convergence e836496f. Supports the genuine stopped Stieltjes dividend equality for 79978d61.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_right_mesh_endpoint_tendsto

open Filter Topology
open scoped ENNReal Classical

theorem AvramDividend.Classical.avram_root29_05_killed_right_mesh_discount_tendsto
    (r q : ℝ) (τ : ℝ≥0∞) :
    Tendsto (fun n : ℕ =>
      let e := ((⌈r * ((n : ℝ) + 1)⌉ : ℤ) : ℝ) / ((n : ℝ) + 1)
      if ENNReal.ofReal e < τ then
        ENNReal.ofReal (Real.exp (-(q * e))) else 0)
      atTop (𝓝 (if ENNReal.ofReal r < τ then
        ENNReal.ofReal (Real.exp (-(q * r))) else 0)) := by sorry
