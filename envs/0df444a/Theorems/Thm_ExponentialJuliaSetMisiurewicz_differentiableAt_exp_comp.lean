-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_differentiableAt_exp_comp
-- name    : ExponentialJuliaSetMisiurewicz.differentiableAt_exp_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:11.839467+00:00
-- url     : https://prove2.me/theorems/003c904d-bf08-4a31-b801-522193269734
-- title:
--   Exponential Julia Set Misiurewicz: differentiable At exp comp
-- statement:
--   Composition with the exponential preserves complex differentiability at a point.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Basic.lean#L89-L93
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Basic.lean#L89-L93

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

theorem ExponentialJuliaSetMisiurewicz.differentiableAt_exp_comp
    {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) :
    DifferentiableAt ℂ (fun w => Complex.exp (f w)) z := by sorry
