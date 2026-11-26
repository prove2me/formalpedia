-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_deriv_expIterate_succ
-- name    : ExponentialJuliaSetMisiurewicz.deriv_expIterate_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:31.898223+00:00
-- url     : https://prove2.me/theorems/c2ff7810-f624-491d-9f2f-59dadd9bd4e7
-- title:
--   Exponential Julia Set Misiurewicz: deriv exp Iterate succ
-- statement:
--   Derivative recursion for the iterates of the exponential.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Expansion.lean#L36-L52
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Expansion.lean#L36-L52

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Definitions.Def_ExpChaotic_Basic
import Definitions.Def_ExpChaotic_Expansion
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.deriv_expIterate_succ (n : ℕ) (z : ℂ) :
    deriv (expIterate (n + 1)) z =
      deriv (expIterate n) z *
        Complex.exp (expIterate n z) := by sorry
