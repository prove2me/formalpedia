-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_eventually_hits_one_and_two
-- name    : ExponentialJuliaSetMisiurewicz.eventually_hits_one_and_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:46.324795+00:00
-- url     : https://prove2.me/theorems/991f6a8f-de6e-4a2a-88e0-ec13248a5dbf
-- title:
--   Exponential Julia Set Misiurewicz: eventually hits one and two
-- statement:
--   Every sufficiently late iterate of a nonempty open set contains both `1` and `2`.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Spherical.lean#L42-L48
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Spherical.lean#L42-L48

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Definitions.Def_ExpChaotic_Covering
import Definitions.Def_ExpChaotic_Spherical
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.eventually_hits_one_and_two {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ N : ℕ, ∀ n ≥ N,
      (∃ z ∈ U, expIterate n z = 1) ∧ (∃ z ∈ U, expIterate n z = 2) := by sorry
