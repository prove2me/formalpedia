-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_cayleyUp_inv
-- name    : ExponentialJuliaSetMisiurewicz.cayleyUp_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:31.233265+00:00
-- url     : https://prove2.me/theorems/3e8bdfba-b5b3-53ac-b84c-54a5ff332f03
-- title:
--   Exponential Julia Set Misiurewicz: cayley Up inv
-- statement:
--   The Cayley transform of the upper half-plane is inverted by `u ↦ i(1+u)/(1-u)`.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/HalfPlane.lean#L145-L157
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/HalfPlane.lean#L145-L157

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

theorem ExponentialJuliaSetMisiurewicz.cayleyUp_inv {w : ℂ} (hw : w + Complex.I ≠ 0) :
    Complex.I * (1 + (w - Complex.I) / (w + Complex.I))
      / (1 - (w - Complex.I) / (w + Complex.I)) = w := by sorry
