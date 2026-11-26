-- Prove2me | Theorems.Thm_ExpChaotic_not_countable_denseOrbitSet
-- name    : ExpChaotic.not_countable_denseOrbitSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:09:34.969091+00:00
-- url     : https://prove2.me/theorems/30668c2b-59a9-5874-9245-4dc11ed89960
-- title:
--   Exp Chaotic: not countable dense Orbit Set
-- statement:
--   Corollary 5.6. There are uncountably many points with dense forward orbit.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean#L122-L123
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean#L122-L123

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

theorem ExpChaotic.not_countable_denseOrbitSet : ¬ denseOrbitSet.Countable := by sorry
