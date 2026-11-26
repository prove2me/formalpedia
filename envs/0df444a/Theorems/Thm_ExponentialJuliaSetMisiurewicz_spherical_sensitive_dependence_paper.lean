-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_spherical_sensitive_dependence_paper
-- name    : ExponentialJuliaSetMisiurewicz.spherical_sensitive_dependence_paper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:49.758204+00:00
-- url     : https://prove2.me/theorems/e88ce6c8-f53a-4c4f-8cf2-bded6d23ef85
-- title:
--   Exponential Julia Set Misiurewicz: spherical sensitive dependence paper
-- statement:
--   **Corollary 4.4 and Exercise 8.7.** The paper's spherical sensitivity condition holds
--   for every pair of positive constants, at every sufficiently late time.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/PaperConsequences.lean#L49-L67
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/PaperConsequences.lean#L49-L67

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Interval.Set.Infinite
import Definitions.Def_ExpChaotic_Dynamics
import Definitions.Def_ExpChaotic_PaperConsequences
set_option autoImplicit true
open Function Filter Set Metric
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.spherical_sensitive_dependence_paper {U : Set ℂ}
    (hU : IsOpen U) (hUne : U.Nonempty) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ z ∈ U, ∃ w ∈ U,
      ‖expIterate n z‖ ≤ R ∧ δ ≤ ‖expIterate n z - expIterate n w‖ := by sorry
