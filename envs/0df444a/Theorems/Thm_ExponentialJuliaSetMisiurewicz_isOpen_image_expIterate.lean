-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_isOpen_image_expIterate
-- name    : ExponentialJuliaSetMisiurewicz.isOpen_image_expIterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:02.99271+00:00
-- url     : https://prove2.me/theorems/ab2fc42a-49d4-5d14-8af5-306a04ce81ae
-- title:
--   Exponential Julia Set Misiurewicz: is Open image exp Iterate
-- statement:
--   Every iterate is an open map, so images of open sets are open.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L539-L552
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L539-L552

import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_Expansion
import Definitions.Def_ExpChaotic_StripGeometry
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.isOpen_image_expIterate {V : Set ℂ} (hV : IsOpen V) (n : ℕ) :
    IsOpen (expIterate n '' V) := by sorry
