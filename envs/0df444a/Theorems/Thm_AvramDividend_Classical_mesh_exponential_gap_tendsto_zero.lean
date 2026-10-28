-- Prove2me | Theorems.Thm_AvramDividend_Classical_mesh_exponential_gap_tendsto_zero
-- name    : AvramDividend.Classical.mesh_exponential_gap_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:18:21.642136+00:00
-- url     : https://prove2.me/theorems/104a93c5-b33b-42b6-a56a-f0c514ab456d
-- title:
--   A scaled exponential gap tends to zero when its exponent vanishes
-- statement:
--   The exponential deficit of a real sequence tending to zero also tends to zero, even after multiplication by an arbitrary fixed real scalar. This is the analytic limit step for the Levy finite-mesh instantaneous-ruin argument.
-- source:
--   Mathlib continuity of Real.exp and Tendsto subtraction and multiplication.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field

open Filter

theorem AvramDividend.Classical.mesh_exponential_gap_tendsto_zero
    (r : ℕ → ℝ) (C : ℝ)
    (hr : Tendsto r atTop (nhds (0 : ℝ))) :
    Tendsto (fun n : ℕ => C * (1 - Real.exp (-(r n))))
      atTop (nhds (0 : ℝ)) := by sorry
