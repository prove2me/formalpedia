-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_differentiable_expIterate
-- name    : ExponentialJuliaSetMisiurewicz.differentiable_expIterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:10.946039+00:00
-- url     : https://prove2.me/theorems/fc18cdb3-abf4-5fc6-82ae-fae4f188cd9b
-- title:
--   Exponential Julia Set Misiurewicz: differentiable exp Iterate
-- statement:
--   Every iterate of the exponential is complex differentiable.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Basic.lean#L104-L110
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Basic.lean#L104-L110

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

theorem ExponentialJuliaSetMisiurewicz.differentiable_expIterate (n : ℕ) :
    Differentiable ℂ (expIterate n) := by sorry
