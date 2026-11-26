-- Prove2me | Theorems.Thm_ExpChaotic_not_tendstoLocallyUniformlyOn_sphericalExpIterate
-- name    : ExpChaotic.not_tendstoLocallyUniformlyOn_sphericalExpIterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:18:09.503311+00:00
-- url     : https://prove2.me/theorems/0dbdf12a-da19-5775-a6b5-b8013b24baac
-- title:
--   Exp Chaotic: not tendsto Locally Uniformly On spherical Exp Iterate
-- statement:
--   No strictly increasing subsequence of the iterates has a locally uniform spherical
--   limit on a nonempty open set. The limit is allowed to be any sphere-valued function.
--   This directly rules out normality in the sphere-valued formulation, using Mathlib's
--   `TendstoLocallyUniformlyOn`. All iterates have domain `ℂ`.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean#L186-L191
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean#L186-L191

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
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_not_tendstoLocallyUniformlyOn_sphericalExpIterate

set_option autoImplicit true
open Function Filter Set Metric
open ExpChaotic
noncomputable section

theorem ExpChaotic.not_tendstoLocallyUniformlyOn_sphericalExpIterate
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (g : ℂ → RiemannSphere) :
    ¬ TendstoLocallyUniformlyOn (fun n => sphericalExpIterate (φ n)) g atTop U := by sorry
