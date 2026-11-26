-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_noreal_conj_image
-- name    : ExponentialJuliaSetMisiurewicz.noreal_conj_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:58.457772+00:00
-- url     : https://prove2.me/theorems/b9b0b802-f1f1-5ae1-9db6-2891decd5cff
-- title:
--   Exponential Julia Set Misiurewicz: noreal conj image
-- statement:
--   No image of the conjugate meets the real axis if none of `V`'s images does.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/RealAxis.lean#L140-L146
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/RealAxis.lean#L140-L146

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

theorem ExponentialJuliaSetMisiurewicz.noreal_conj_image {V : Set ℂ}
    (hnoreal : ∀ (n : ℕ), ∀ z ∈ V, (expIterate n z).im ≠ 0) :
    ∀ (n : ℕ), ∀ z ∈ (starRingEnd ℂ) '' V, (expIterate n z).im ≠ 0 := by sorry
