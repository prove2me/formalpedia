-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_isConnected_conj_image
-- name    : ExponentialJuliaSetMisiurewicz.isConnected_conj_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:07:16.87156+00:00
-- url     : https://prove2.me/theorems/8fc92890-7777-47aa-bbce-3130b138a9ad
-- title:
--   Exponential Julia Set Misiurewicz: is Connected conj image
-- statement:
--   Complex conjugation sends connected sets to connected sets.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/RealAxis.lean#L131-L133
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/RealAxis.lean#L131-L133

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

theorem ExponentialJuliaSetMisiurewicz.isConnected_conj_image {V : Set ℂ} (hV : IsConnected V) :
    IsConnected ((starRingEnd ℂ) '' V) := by sorry
