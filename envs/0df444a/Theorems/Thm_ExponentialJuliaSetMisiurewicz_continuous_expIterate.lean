-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_continuous_expIterate
-- name    : ExponentialJuliaSetMisiurewicz.continuous_expIterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:14.621391+00:00
-- url     : https://prove2.me/theorems/1b282cc3-3901-4dfe-a0f8-39383158eca2
-- title:
--   Exponential Julia Set Misiurewicz: continuous exp Iterate
-- statement:
--   Every iterate of the exponential is continuous.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Basic.lean#L113-L115
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Basic.lean#L113-L115

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Definitions.Def_ExpChaotic_Basic
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.continuous_expIterate (n : ℕ) :
    Continuous (expIterate n) := by sorry
