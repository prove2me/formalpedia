-- Prove2me | Theorems.Thm_Autoconvolutions_integral_auto_step
-- name    : Autoconvolutions.integral_auto_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:59.0091+00:00
-- url     : https://prove2.me/theorems/6678c7db-00c2-4b93-8495-0ce0a83d7841
-- title:
--   Autoconvolutions: integral auto step
-- statement:
--   Fubini for scalar convolution gives the paper's identity F(1)².
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Step.lean#L52-L58
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Step.lean#L52-L58

module
public import Definitions.Def_Autoconvolutions_Definitions
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Convolution
public import Definitions.Def_Autoconvolutions_Step
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped ENNReal BigOperators
open Autoconvolutions

theorem Autoconvolutions.integral_auto_step (d : ℕ) (p : Fin (d + 1) → ℝ) :
    (∫ x : ℝ, auto (step d p) x) = (∑ j, p j) ^ 2 := by sorry
