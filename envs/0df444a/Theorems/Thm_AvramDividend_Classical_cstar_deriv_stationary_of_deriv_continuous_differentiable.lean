-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_deriv_stationary_of_deriv_continuous_differentiable
-- name    : AvramDividend.Classical.cstar_deriv_stationary_of_deriv_continuous_differentiable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T07:19:34.155901+00:00
-- url     : https://prove2.me/theorems/5a07cd39-94d5-4b4c-a7ce-4b8c732f8c86
-- title:
--   At a positive canonical barrier the scale derivative is stationary whenever differentiable
-- statement:
--   If the ordinary derivative of W is continuous on positive reserves, the canonical optimal barrier is positive, and W' is differentiable at that barrier, then W' has derivative zero there in the precise Lean HasDerivAt sense. This follows from the already Proved canonical-barrier minimiser theorem and Fermat's theorem, and provides the exact hWstat argument required by the existing Proved second-order smooth-fit transfer for vcstar.

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_toReal_zero_or_minimal_of_deriv_continuous

open Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.cstar_deriv_stationary_of_deriv_continuous_differentiable
    (W : ℝ → ℝ)
    (hcont : ContinuousOn (deriv W) (Ioi 0))
    (hpos : 0 < (cstar W).toReal)
    (hdiff : DifferentiableAt ℝ (deriv W) (cstar W).toReal) :
    HasDerivAt (deriv W) 0 (cstar W).toReal := by sorry
