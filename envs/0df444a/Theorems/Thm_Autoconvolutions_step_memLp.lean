-- Prove2me | Theorems.Thm_Autoconvolutions_step_memLp
-- name    : Autoconvolutions.step_memLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:52.873796+00:00
-- url     : https://prove2.me/theorems/19a290d0-7cbc-4b22-8136-1efff61d6408
-- title:
--   Autoconvolutions: step mem Lp
-- statement:
--   Every finite unit-cell input is in every Lᵖ space, including L¹ and L².
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Step.lean#L17-L22
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Step.lean#L17-L22

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

theorem Autoconvolutions.step_memLp (d : ℕ) (p : Fin (d + 1) → ℝ) (q : ℝ≥0∞) :
    MemLp (step d p) q volume := by sorry
