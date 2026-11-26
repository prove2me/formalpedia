-- Prove2me | Theorems.Thm_ExpChaotic_dense_repellingPeriodicSet
-- name    : ExpChaotic.dense_repellingPeriodicSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:09:48.693534+00:00
-- url     : https://prove2.me/theorems/a41fcaf5-89a8-5d77-bdeb-82ed6b23b1e1
-- title:
--   Exp Chaotic: dense repelling Periodic Set
-- statement:
--   Theorem 1.1, part 3., and Theorem 6.1: (Repelling) periodic points are dense.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean#L126-L127
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean#L126-L127

import Mathlib.Dynamics.Transitive
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Exponential
import Mathlib.GroupTheory.GroupAction.IterateAct
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Definitions.Def_ExpChaotic_Normality
import Definitions.Def_ExpChaotic_PaperConsequences
import Definitions.Def_ExpChaotic_Spherical
import Definitions.Def_ExpChaotic_Results
set_option autoImplicit true
open Function Filter Set Metric
open ExpChaotic
noncomputable section

theorem ExpChaotic.dense_repellingPeriodicSet : Dense repellingPeriodicSet := by sorry
