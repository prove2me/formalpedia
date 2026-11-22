-- Prove2me | Theorems.Thm_Autoconvolutions_integral_step
-- name    : Autoconvolutions.integral_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:55.746771+00:00
-- url     : https://prove2.me/theorems/b5c60d6f-ec92-4747-91f3-1cc77fa1a69f
-- title:
--   Autoconvolutions: integral step
-- statement:
--   Unit cells have Lebesgue measure one, so their coefficients add without weights.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Step.lean#L31-L40
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Step.lean#L31-L40

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

theorem Autoconvolutions.integral_step (d : ℕ) (p : Fin (d + 1) → ℝ) :
    (∫ x : ℝ, step d p x) = ∑ j, p j := by sorry
