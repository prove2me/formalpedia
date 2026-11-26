-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_differentiableOn_expIterate
-- name    : ExponentialJuliaSetMisiurewicz.differentiableOn_expIterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:14.309484+00:00
-- url     : https://prove2.me/theorems/15986cc4-7856-4446-904c-374489a0b87f
-- title:
--   Exponential Julia Set Misiurewicz: differentiable On exp Iterate
-- statement:
--   Every iterate of the exponential is complex differentiable on every set.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Basic.lean#L118-L120
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Basic.lean#L118-L120

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

theorem ExponentialJuliaSetMisiurewicz.differentiableOn_expIterate (n : ℕ) (s : Set ℂ) :
    DifferentiableOn ℂ (expIterate n) s := by sorry
