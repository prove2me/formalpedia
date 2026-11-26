-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_exists_re_gt_four_of_real
-- name    : ExponentialJuliaSetMisiurewicz.exists_re_gt_four_of_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:56.114076+00:00
-- url     : https://prove2.me/theorems/997f1ac1-b20b-4c79-a7ff-8df0bd257be0
-- title:
--   Exponential Julia Set Misiurewicz: exists re gt four of real
-- statement:
--   A real point's orbit escapes to the right: some iterate has real part exceeding `4`.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/RealAxis.lean#L186-L191
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/RealAxis.lean#L186-L191

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

theorem ExponentialJuliaSetMisiurewicz.exists_re_gt_four_of_real {p : ℂ} (hp : p.im = 0) :
    ∃ m : ℕ, 4 < (expIterate m p).re := by sorry
