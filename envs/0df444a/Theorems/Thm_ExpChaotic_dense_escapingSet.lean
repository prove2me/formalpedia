-- Prove2me | Theorems.Thm_ExpChaotic_dense_escapingSet
-- name    : ExpChaotic.dense_escapingSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:09:28.622804+00:00
-- url     : https://prove2.me/theorems/13a739a6-abf7-4203-98eb-952ad02f3672
-- title:
--   Exp Chaotic: dense escaping Set
-- statement:
--   Theorem 1.1, part 1., and Theorem 4.1: Escaping points are dense.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean#L114-L115
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean#L114-L115

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

theorem ExpChaotic.dense_escapingSet : Dense escapingSet := by sorry
