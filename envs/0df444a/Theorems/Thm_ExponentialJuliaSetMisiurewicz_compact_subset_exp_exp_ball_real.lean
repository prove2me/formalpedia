-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_compact_subset_exp_exp_ball_real
-- name    : ExponentialJuliaSetMisiurewicz.compact_subset_exp_exp_ball_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:03:24.778066+00:00
-- url     : https://prove2.me/theorems/6f70fcc7-bd15-4914-9e3a-eb973226a6ad
-- title:
--   Exponential Julia Set Misiurewicz: compact subset exp exp ball real
-- statement:
--   Compactness makes the preceding elementary covering estimate uniform.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Covering.lean#L166-L176
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Covering.lean#L166-L176

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_RealAxis
import Definitions.Def_ExpChaotic_Covering
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.compact_subset_exp_exp_ball_real {K : Set ℂ}
    (hK : IsCompact K) (hK0 : (0 : ℂ) ∉ K) :
    ∃ ρ : ℝ, ∀ x : ℝ, ρ ≤ x → K ⊆ expIterate 2 '' ball (x : ℂ) 8 := by sorry
