-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_cayleyDown_inv
-- name    : ExponentialJuliaSetMisiurewicz.cayleyDown_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:06:28.103112+00:00
-- url     : https://prove2.me/theorems/6881f5d1-7f1f-565a-8311-e9bb908ecbd7
-- title:
--   Exponential Julia Set Misiurewicz: cayley Down inv
-- statement:
--   The Cayley transform of the lower half-plane is inverted by `u ↦ i(u+1)/(u-1)`.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/HalfPlane.lean#L160-L172
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/HalfPlane.lean#L160-L172

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Definitions.Def_ExpChaotic_StripGeometry
import Definitions.Def_ExpChaotic_HalfPlane
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.cayleyDown_inv {w : ℂ} (hw : w - Complex.I ≠ 0) :
    Complex.I * (1 + (w + Complex.I) / (w - Complex.I))
      / ((w + Complex.I) / (w - Complex.I) - 1) = w := by sorry
