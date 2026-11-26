-- Prove2me | Theorems.Thm_ExpChaotic_dense_iteratedPreimages_realAxis
-- name    : ExpChaotic.dense_iteratedPreimages_realAxis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:09:12.881312+00:00
-- url     : https://prove2.me/theorems/8f2c1308-e2c9-5f45-9ee7-389d1b74026f
-- title:
--   Exp Chaotic: dense iterated Preimages real Axis
-- statement:
--   The full iterated preimage of the real axis is dense.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean#L108-L111
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean#L108-L111

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

theorem ExpChaotic.dense_iteratedPreimages_realAxis :
    Dense {z : ℂ | ∃ n : ℕ, (expIterate n z).im = 0} := by sorry
