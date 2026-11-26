-- Prove2me | Theorems.Thm_ExpChaotic_eventually_covers_compact
-- name    : ExpChaotic.eventually_covers_compact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:15:58.015498+00:00
-- url     : https://prove2.me/theorems/0fb5f184-7d99-4d20-84e7-863501c1d126
-- title:
--   Exp Chaotic: eventually covers compact
-- statement:
--   Corollary 5.5. Given a prescribed compact set K that omits zero,
--   every sufficiently high iterate of a nonempty open set covers K.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean#L96-L100
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean#L96-L100

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
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_eventually_covers_compact

set_option autoImplicit true
open Function Filter Set Metric
open ExpChaotic
noncomputable section

theorem ExpChaotic.eventually_covers_compact
    {U K : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    (hK : IsCompact K) (hK0 : (0 : ℂ) ∉ K) :
    ∃ N : ℕ, ∀ n : ℕ, (n ≥ N → K ⊆ expIterate n '' U) := by sorry
