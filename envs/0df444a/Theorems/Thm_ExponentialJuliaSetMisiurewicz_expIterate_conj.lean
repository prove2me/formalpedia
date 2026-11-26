-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_conj
-- name    : ExponentialJuliaSetMisiurewicz.expIterate_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:54.247663+00:00
-- url     : https://prove2.me/theorems/6f6bf1e0-1d9c-420a-a7d5-5bf8505e746d
-- title:
--   Exponential Julia Set Misiurewicz: exp Iterate conj
-- statement:
--   Conjugation commutes with the iterates of `exp`.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/RealAxis.lean#L106-L112
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/RealAxis.lean#L106-L112

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

theorem ExponentialJuliaSetMisiurewicz.expIterate_conj (n : ℕ) (z : ℂ) :
    expIterate n ((starRingEnd ℂ) z) = (starRingEnd ℂ) (expIterate n z) := by sorry
