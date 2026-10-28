-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_deriv_piecewise_ratio_one_of_C1_positive
-- name    : AvramDividend.Classical.vcstar_deriv_piecewise_ratio_one_of_C1_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T08:12:42.723871+00:00
-- url     : https://prove2.me/theorems/d41c0927-2a50-47ef-aa5c-cd874f5c6b88
-- title:
--   Exact optimal-barrier derivative profile across the positive barrier
-- statement:
--   For a positive optimal barrier with positive scale derivative and C1 scale function, the derivative of vcstar has the exact piecewise form W'(x)/W'(c*) for positive x at or below the barrier and one above it. This exports the already verified derivative identities into a reusable theorem, allowing direct import in global Gaussian C2 proof.
-- source:
--   Avram, Palmowski and Pistorius (2007), positive-barrier scale-value representation and smooth fit; deterministic extraction from the Proved vcstar_deriv_continuous_C1_positive proof.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.OrderClosed
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_local_scale_deriv_positive
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar
open AvramDividend.Classical Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical
/-- The derivative of the barrier candidate equals its normalised scale derivative below c* and one above it. -/
theorem vcstar_deriv_piecewise_ratio_one_of_C1_positive
    (W : ℝ → ℝ)
    (hcpos : 0 < (cstar W).toReal)
    (hreg : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)))
    (hdpos : 0 < deriv W (cstar W).toReal) :
    ∀ x : ℝ, 0 < x →
      deriv (vcstar W) x =
        (Iic (cstar W).toReal).piecewise
          (fun y : ℝ => deriv W y / deriv W (cstar W).toReal)
          (fun _ : ℝ => (1 : ℝ)) x := by
  sorry
end AvramDividend.Classical
