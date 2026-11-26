-- Prove2me | Theorems.Thm_ExpChaotic_not_equicontinuousAt_sphericalExpIterate
-- name    : ExpChaotic.not_equicontinuousAt_sphericalExpIterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:18:51.60046+00:00
-- url     : https://prove2.me/theorems/e9551e87-90bb-5325-9420-a940d38f6a60
-- title:
--   Exp Chaotic: not equicontinuous At spherical Exp Iterate
-- statement:
--   Corollary 4.4 (reformulated): The sphere-valued iterates are not equicontinuous
--   at any point of the plane.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean#L141-L143
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean#L141-L143

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
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_not_equicontinuousAt_sphericalExpIterate

set_option autoImplicit true
open Function Filter Set Metric
open ExpChaotic
noncomputable section

theorem ExpChaotic.not_equicontinuousAt_sphericalExpIterate (z : ℂ) :
    ¬ EquicontinuousAt sphericalExpIterate z := by sorry
