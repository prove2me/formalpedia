-- Prove2me | Theorems.Thm_Autoconvolutions_auto_step_nonneg
-- name    : Autoconvolutions.auto_step_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:04.050694+00:00
-- url     : https://prove2.me/theorems/d9976ec5-caed-4c3b-83f4-b8ccb158ac93
-- title:
--   Autoconvolutions: auto step nonneg
-- statement:
--   The Autoconvolutions construction uses the auto step nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Step.lean#L47-L49
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Step.lean#L47-L49

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

theorem Autoconvolutions.auto_step_nonneg {d : ℕ} {p : Fin (d + 1) → ℝ} (hp : ∀ j, 0 ≤ p j) (x : ℝ) :
    0 ≤ auto (step d p) x := by sorry
