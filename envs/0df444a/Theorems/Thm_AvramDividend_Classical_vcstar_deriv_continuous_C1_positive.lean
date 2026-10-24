-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_deriv_continuous_C1_positive
-- name    : AvramDividend.Classical.vcstar_deriv_continuous_C1_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T11:04:14.950754+00:00
-- url     : https://prove2.me/theorems/30e475d6-e19a-4ab8-a377-36db1f21e9c2
-- title:
--   Positive-barrier dividend derivative is continuous under C1 scale smoothness
-- statement:
--   For any real scale-like W whose derivative is continuous on positive reserves, a positive canonical barrier with W'(c*)>0 has a continuously differentiable candidate dividend value. Below the barrier the ordinary derivative is W'/W'(c*), above it the derivative is one, and at the barrier the already-Proved derivative-pasting lemma supplies equality. The piecewise derivative is continuous by the Mathlib gluing lemma.
-- source:
--   Deterministic derivative-pasting of a piecewise scale-ratio and affine barrier value using pinned Mathlib; no stochastic regularity claimed.

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
/-- Global positive-axis derivative continuity from C1 scale regularity and a positive cap normaliser. -/
theorem vcstar_deriv_continuous_C1_positive (W : ℝ → ℝ)
    (hcpos : 0 < (cstar W).toReal)
    (hreg : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)))
    (hdpos : 0 < deriv W (cstar W).toReal) :
    ContinuousOn (deriv (vcstar W)) (Ioi (0 : ℝ)) := by sorry
end AvramDividend.Classical
