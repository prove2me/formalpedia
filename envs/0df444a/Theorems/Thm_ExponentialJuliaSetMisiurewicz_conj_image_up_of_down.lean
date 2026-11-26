-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_conj_image_up_of_down
-- name    : ExponentialJuliaSetMisiurewicz.conj_image_up_of_down
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:57.462064+00:00
-- url     : https://prove2.me/theorems/47efa502-34a6-50c2-9d50-8fa88e3f0ce9
-- title:
--   Exponential Julia Set Misiurewicz: conj image up of down
-- statement:
--   Times at which `V` lands in the lower half-plane are times at which the conjugate lands
--   in the upper one.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/RealAxis.lean#L150-L156
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/RealAxis.lean#L150-L156

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Definitions.Def_ExpChaotic_HalfPlane
import Definitions.Def_ExpChaotic_RealAxis
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.conj_image_up_of_down {V : Set ℂ} {n : ℕ}
    (h : ∀ z ∈ V, (expIterate n z).im < 0) :
    ∀ z ∈ (starRingEnd ℂ) '' V, 0 < (expIterate n z).im := by sorry
