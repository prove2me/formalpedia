-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma6_eventually_meets_disc
-- name    : ExponentialJuliaSetMisiurewicz.lemma6_eventually_meets_disc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:41.534781+00:00
-- url     : https://prove2.me/theorems/b2a86ed6-4b0c-508f-b595-ab0150288fbc
-- title:
--   Exponential Julia Set Misiurewicz: lemma6 eventually meets disc
-- statement:
--   Harrison's auxiliary step inside `LEMMA_6`: if no forward image of `V` meets the real
--   axis, then all but finitely many images meet the disc of radius `exp 4`.
--
--   Contrapositive of Lemma 5: only finitely many images can sit inside the right half-plane, and
--   if the image at time `n` misses the disc then the image at time `n - 1` lay in the half-plane,
--   since `‖exp z‖ = exp (Re z)`.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/RealAxis.lean#L41-L70
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/RealAxis.lean#L41-L70

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

theorem ExponentialJuliaSetMisiurewicz.lemma6_eventually_meets_disc
    {V : Set ℂ} (hVopen : IsOpen V) (hVconn : IsConnected V) (hVne : V.Nonempty)
    (hnoreal : ∀ (n : ℕ), ∀ z ∈ V, (expIterate n z).im ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N,
      (expIterate n '' V ∩ closedBall (0 : ℂ) (Real.exp 4)).Nonempty := by sorry
