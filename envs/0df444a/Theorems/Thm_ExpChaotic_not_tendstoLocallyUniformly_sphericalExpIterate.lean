-- Prove2me | Theorems.Thm_ExpChaotic_not_tendstoLocallyUniformly_sphericalExpIterate
-- name    : ExpChaotic.not_tendstoLocallyUniformly_sphericalExpIterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:10:11.262587+00:00
-- url     : https://prove2.me/theorems/151ffa32-2cdf-4f95-86a6-6171596045be
-- title:
--   Exp Chaotic: not tendsto Locally Uniformly spherical Exp Iterate
-- statement:
--   No increasing subsequence of the iterates has a locally uniform spherical limit
--   on a nonempty open set. The arbitrary sphere-valued limit is defined only on that set.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean#L170-L176
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean#L170-L176

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

theorem ExpChaotic.not_tendstoLocallyUniformly_sphericalExpIterate
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (g : U → RiemannSphere) :
    ¬ TendstoLocallyUniformly (fun n (z : U) => sphericalExpIterate (φ n) z) g atTop := by sorry
