-- Prove2me | Theorems.Thm_ExpChaotic_dense_denseOrbitSet
-- name    : ExpChaotic.dense_denseOrbitSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:09:32.04391+00:00
-- url     : https://prove2.me/theorems/cfe7e80c-c98c-4d72-aef1-e820030d4a9a
-- title:
--   Exp Chaotic: dense dense Orbit Set
-- statement:
--   Theorem 1.1, part 2.: Points with dense forward orbit are dense.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean#L118-L119
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean#L118-L119

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

theorem ExpChaotic.dense_denseOrbitSet : Dense denseOrbitSet := by sorry
