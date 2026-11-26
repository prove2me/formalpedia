-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_norm_sub_lt_of_cayley_close
-- name    : ExponentialJuliaSetMisiurewicz.norm_sub_lt_of_cayley_close
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:50.010819+00:00
-- url     : https://prove2.me/theorems/e83c75bf-cde8-4be3-a509-52f4aad61249
-- title:
--   Exponential Julia Set Misiurewicz: norm sub lt of cayley close
-- statement:
--   **Push-back.** Near a finite point `p ≠ -i`, closeness of Cayley
--   transforms gives closeness of the points themselves. This is what converts the equicontinuity
--   of the transformed family back into Euclidean information about the iterates.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/HalfPlane.lean#L259-L281
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/HalfPlane.lean#L259-L281

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

theorem ExponentialJuliaSetMisiurewicz.norm_sub_lt_of_cayley_close
    {p : ℂ} (hp : p + Complex.I ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ∀ w : ℂ, w + Complex.I ≠ 0 →
      ‖(w - Complex.I) / (w + Complex.I) - (p - Complex.I) / (p + Complex.I)‖ < ε →
      ‖w - p‖ < η := by sorry
