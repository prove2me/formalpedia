-- Prove2me | Theorems.Thm_ExpChaotic_dense_iteratedPreimages_nonzero
-- name    : ExpChaotic.dense_iteratedPreimages_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:09:10.032429+00:00
-- url     : https://prove2.me/theorems/806f8bc3-a4a7-5f0b-b593-f4c91f5fb480
-- title:
--   Exp Chaotic: dense iterated Preimages nonzero
-- statement:
--   The full iterated preimage of every nonzero point is dense.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean#L103-L105
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean#L103-L105

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

theorem ExpChaotic.dense_iteratedPreimages_nonzero {w : ℂ} (hw : w ≠ 0) :
    Dense {z : ℂ | ∃ n : ℕ, expIterate n z = w} := by sorry
