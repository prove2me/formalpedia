-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_im_eq_zero_of_le
-- name    : ExponentialJuliaSetMisiurewicz.expIterate_im_eq_zero_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:27.293802+00:00
-- url     : https://prove2.me/theorems/63ad45ab-3a20-4ce4-9571-7795510d1e7d
-- title:
--   Exponential Julia Set Misiurewicz: exp Iterate im eq zero of le
-- statement:
--   If an orbit point is real, all later orbit points are real.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L37-L45
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L37-L45

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

theorem ExponentialJuliaSetMisiurewicz.expIterate_im_eq_zero_of_le {z : ℂ} {n : ℕ} (h : (expIterate n z).im = 0) :
    ∀ m, n ≤ m → (expIterate m z).im = 0 := by sorry
