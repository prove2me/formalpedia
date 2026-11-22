-- Prove2me | Theorems.Thm_Autoconvolutions_auto_step_interpolate
-- name    : Autoconvolutions.auto_step_interpolate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:24.385924+00:00
-- url     : https://prove2.me/theorems/25db2700-2a46-4e0f-be8e-77d95f0877ca
-- title:
--   Autoconvolutions: auto step interpolate
-- statement:
--   Linear interpolation on every lattice interval, including the outer zero cells.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Interpolation.lean#L127-L142
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Interpolation.lean#L127-L142

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

theorem Autoconvolutions.auto_step_interpolate (d : ℕ) (p : Fin (d+1) → ℝ) (k : ℤ)
    (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1) :
    auto (step d p) ((k:ℝ)+1+u) = (1-u)*convCoeff d p k + u*convCoeff d p (k+1) := by sorry
