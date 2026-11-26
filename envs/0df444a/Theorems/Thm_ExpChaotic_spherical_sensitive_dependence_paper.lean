-- Prove2me | Theorems.Thm_ExpChaotic_spherical_sensitive_dependence_paper
-- name    : ExpChaotic.spherical_sensitive_dependence_paper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:17:28.519714+00:00
-- url     : https://prove2.me/theorems/89adbfab-09c1-4d41-b1a4-23d6717b0023
-- title:
--   Exp Chaotic: spherical sensitive dependence paper
-- statement:
--   Corollary 4.4, in the precise form of Definition 2.3. The arbitrary positive constants
--   give Exercise 8.7 as well; the conclusion even holds at every sufficiently late time.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean#L154-L158
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Results.lean#L154-L158

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
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_spherical_sensitive_dependence_paper

set_option autoImplicit true
open Function Filter Set Metric
open ExpChaotic
noncomputable section

theorem ExpChaotic.spherical_sensitive_dependence_paper {U : Set ℂ}
    (hU : IsOpen U) (hUne : U.Nonempty) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, (n ≥ N → ∃ z ∈ U, ∃ w ∈ U,
      ‖expIterate n z‖ ≤ R ∧ δ ≤ ‖expIterate n z - expIterate n w‖) := by sorry
