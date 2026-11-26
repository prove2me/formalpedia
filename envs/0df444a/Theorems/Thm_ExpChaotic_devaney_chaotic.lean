-- Prove2me | Theorems.Thm_ExpChaotic_devaney_chaotic
-- name    : ExpChaotic.devaney_chaotic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:09:59.521805+00:00
-- url     : https://prove2.me/theorems/348a42bc-db25-46bc-ae5f-29412a68a5a1
-- title:
--   Exp Chaotic: devaney chaotic
-- statement:
--   Theorem 1.2. The exponential map is chaotic in Devaney's sense.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean#L136-L137
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean#L136-L137

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

theorem ExpChaotic.devaney_chaotic : IsDevaneyChaotic Complex.exp := by sorry
