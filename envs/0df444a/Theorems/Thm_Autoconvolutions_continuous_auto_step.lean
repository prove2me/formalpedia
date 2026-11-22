-- Prove2me | Theorems.Thm_Autoconvolutions_continuous_auto_step
-- name    : Autoconvolutions.continuous_auto_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:32.684847+00:00
-- url     : https://prove2.me/theorems/839449ab-c389-40f7-93d9-b52d54b8df24
-- title:
--   Autoconvolutions: continuous auto step
-- statement:
--   The Autoconvolutions construction uses the continuous auto step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Interpolation.lean#L79-L82
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Interpolation.lean#L79-L82

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

theorem Autoconvolutions.continuous_auto_step (d : ℕ) (p : Fin (d+1) → ℝ) : Continuous (auto (step d p)) := by sorry
