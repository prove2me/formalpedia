-- Prove2me | Theorems.Thm_ExpChaotic_infinitely_often_hits_negative_realAxis
-- name    : ExpChaotic.infinitely_often_hits_negative_realAxis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:18:11.289666+00:00
-- url     : https://prove2.me/theorems/ea9dbef1-c17d-4685-a0e2-07d020ea0c19
-- title:
--   Exp Chaotic: infinitely often hits negative real Axis
-- statement:
--   Theorem 4.3: infinitely many iterated images of a nonempty open set meet the
--   negative real axis. Strict negativity strengthens the nonpositive-axis statement in the paper.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean#L147-L150
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean#L147-L150

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
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_infinitely_often_hits_negative_realAxis

set_option autoImplicit true
open Function Filter Set Metric
open ExpChaotic
noncomputable section

theorem ExpChaotic.infinitely_often_hits_negative_realAxis {U : Set ℂ}
    (hU : IsOpen U) (hUne : U.Nonempty) :
    {n : ℕ | ∃ z ∈ U, (expIterate n z).im = 0 ∧ (expIterate n z).re < 0}.Infinite := by sorry
