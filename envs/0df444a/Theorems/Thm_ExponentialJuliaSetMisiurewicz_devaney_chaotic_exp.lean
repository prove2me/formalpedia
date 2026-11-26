-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_devaney_chaotic_exp
-- name    : ExponentialJuliaSetMisiurewicz.devaney_chaotic_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:04:23.294154+00:00
-- url     : https://prove2.me/theorems/325c9569-c775-440e-9f6d-9d8b2016dcbc
-- title:
--   Exponential Julia Set Misiurewicz: devaney chaotic exp
-- statement:
--   **Theorem 1.2.** The complex exponential map is chaotic in Devaney's sense.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Dynamics.lean#L202-L203
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Dynamics.lean#L202-L203

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

theorem ExponentialJuliaSetMisiurewicz.devaney_chaotic_exp : IsDevaneyChaotic Complex.exp := by sorry
