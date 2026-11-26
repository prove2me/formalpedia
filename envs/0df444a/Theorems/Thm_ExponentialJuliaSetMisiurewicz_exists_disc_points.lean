-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_exists_disc_points
-- name    : ExponentialJuliaSetMisiurewicz.exists_disc_points
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:47.340714+00:00
-- url     : https://prove2.me/theorems/ff0920cd-fd6d-47f0-ba18-12a24b81bc5e
-- title:
--   Exponential Julia Set Misiurewicz: exists disc points
-- statement:
--   Along all large times, the ball contains a point whose image stays in the disc of radius
--   `exp 4`.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/RealAxis.lean#L87-L101
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/RealAxis.lean#L87-L101

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

theorem ExponentialJuliaSetMisiurewicz.exists_disc_points
    {V : Set ℂ}
    (hnoreal : ∀ (n : ℕ), ∀ z ∈ V, (expIterate n z).im ≠ 0)
    {c : ℂ} {σ : ℝ} (hσ : 0 < σ) (hsub : ball c σ ⊆ V) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∃ y ∈ ball c σ, ‖expIterate n y‖ ≤ Real.exp 4 := by sorry
