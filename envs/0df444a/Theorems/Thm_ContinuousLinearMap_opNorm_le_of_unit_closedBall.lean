-- Prove2me | Theorems.Thm_ContinuousLinearMap_opNorm_le_of_unit_closedBall
-- name    : ContinuousLinearMap.opNorm_le_of_unit_closedBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:14:59.302645+00:00
-- url     : https://prove2.me/theorems/4af17dac-ffab-42b7-9fd3-256b0f83178e
-- title:
--   Continuous Linear Map: op Norm le of unit closed Ball
-- statement:
--   A bound on the closed unit ball bounds the operator norm:
--   if `‖f x‖ ≤ C` for every `x` with `‖x‖ ≤ 1`, then `‖f‖ ≤ C`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/QuotientMapNorms.lean#L50-L55
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/QuotientMapNorms.lean#L50-L55

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Group.Quotient
public import Definitions.Def_SNumbers_QuotientMapNorms
set_option autoImplicit true
@[expose] public section
public section
open ContinuousLinearMap
variable {𝕜' : Type*} [DenselyNormedField 𝕜']
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜' E]
variable [SeminormedAddCommGroup F] [NormedSpace 𝕜' F]

theorem ContinuousLinearMap.opNorm_le_of_unit_closedBall (f : E →L[𝕜'] F) {C : ℝ}
    (h : ∀ x : E, ‖x‖ ≤ 1 → ‖f x‖ ≤ C) : ‖f‖ ≤ C := by sorry
