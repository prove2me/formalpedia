-- Prove2me | Theorems.Thm_Autoconvolutions_integral_cell_mul_cell
-- name    : Autoconvolutions.integral_cell_mul_cell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:21.521857+00:00
-- url     : https://prove2.me/theorems/bb614e63-bf24-432d-8743-0c8e5ace6f4d
-- title:
--   Autoconvolutions: integral cell mul cell
-- statement:
--   The genuine Bochner convolution of two unit cells is their translated tent.
--   The two potentially exceptional endpoints of the integrand have measure zero.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Interpolation.lean#L50-L58
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Interpolation.lean#L50-L58

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

theorem Autoconvolutions.integral_cell_mul_cell (a b v w x : ℝ) :
    (∫ t, cell a v t * cell b w (x-t)) = v*w*tent (x-a-b) := by sorry
