-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_mem_denseOrbitSetExp_iff_visit_countableBasis
-- name    : ExponentialJuliaSetMisiurewicz.mem_denseOrbitSetExp_iff_visit_countableBasis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:18.934837+00:00
-- url     : https://prove2.me/theorems/1a543a67-9cba-54e4-9550-89646ba2b1af
-- title:
--   Exponential Julia Set Misiurewicz: mem dense Orbit Set Exp iff visit countable Basis
-- statement:
--   Visiting every member of mathlib's countable basis is equivalent to having dense orbit.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Dynamics.lean#L116-L136
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Dynamics.lean#L116-L136

import Mathlib.Dynamics.Transitive
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.GroupTheory.GroupAction.IterateAct
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Definitions.Def_ExpChaotic_Periodic
import Definitions.Def_ExpChaotic_Dynamics
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.mem_denseOrbitSetExp_iff_visit_countableBasis {z : ℂ} :
    z ∈ denseOrbitSetExp ↔
      z ∈ ⋂ U : TopologicalSpace.countableBasis ℂ, orbitVisitSet U := by sorry
