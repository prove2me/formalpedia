-- Prove2me | Theorems.Thm_ExpChaotic_expansion_along_escaping_orbits
-- name    : ExpChaotic.expansion_along_escaping_orbits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:09:52.270965+00:00
-- url     : https://prove2.me/theorems/73155009-1dec-50ae-b3ad-7556a4c0a078
-- title:
--   Exp Chaotic: expansion along escaping orbits
-- statement:
--   Observation 5.2: along any escaping orbit, the real parts and the norms of the
--   derivatives of the iterates both tend to positive infinity.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean#L162-L166
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean#L162-L166

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

theorem ExpChaotic.expansion_along_escaping_orbits {z : ℂ} (hz : EscapesToInfinity z) :
    Tendsto (fun n => (expIterate n z).re) atTop atTop ∧
      Tendsto (fun n => ‖deriv (expIterate n) z‖) atTop atTop := by sorry
