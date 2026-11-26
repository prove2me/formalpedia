-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_real_orbit
-- name    : ExponentialJuliaSetMisiurewicz.expIterate_real_orbit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:54.392551+00:00
-- url     : https://prove2.me/theorems/45b53257-5b10-48a4-bc43-f430460a9faf
-- title:
--   Exponential Julia Set Misiurewicz: exp Iterate real orbit
-- statement:
--   The orbit of a real point stays real and its real part grows by at least `1` each step.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/RealAxis.lean#L172-L183
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/RealAxis.lean#L172-L183

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

theorem ExponentialJuliaSetMisiurewicz.expIterate_real_orbit {p : ℂ} (hp : p.im = 0) (m : ℕ) :
    (expIterate m p).im = 0 ∧ p.re + m ≤ (expIterate m p).re := by sorry
