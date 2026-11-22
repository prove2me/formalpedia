-- Prove2me | Theorems.Thm_Autoconvolutions_auto_step_tents
-- name    : Autoconvolutions.auto_step_tents
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:37.33797+00:00
-- url     : https://prove2.me/theorems/c9358653-e362-4743-bb37-e43201a03134
-- title:
--   Autoconvolutions: auto step tents
-- statement:
--   Expansion of the analytic convolution into translates of the unit tent.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Interpolation.lean#L65-L77
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Interpolation.lean#L65-L77

module
public import Definitions.Def_Autoconvolutions_Definitions
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic
public import Definitions.Def_Autoconvolutions_Interpolation
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators
open Autoconvolutions

theorem Autoconvolutions.auto_step_tents (d : ℕ) (p : Fin (d+1) → ℝ) (x : ℝ) :
    auto (step d p) x = ∑ i, ∑ j, p i*p j*tent (x-i.val-j.val) := by sorry
