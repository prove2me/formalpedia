-- Prove2me | Theorems.Thm_Autoconvolutions_step_nonneg
-- name    : Autoconvolutions.step_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:52.933305+00:00
-- url     : https://prove2.me/theorems/6fd55372-04e9-4fd8-8a57-6dc75440fa17
-- title:
--   Autoconvolutions: step nonneg
-- statement:
--   The Autoconvolutions construction uses the step nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Step.lean#L24-L28
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Step.lean#L24-L28

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

theorem Autoconvolutions.step_nonneg (d : ℕ) (p : Fin (d + 1) → ℝ) (hp : ∀ j, 0 ≤ p j) (x : ℝ) :
    0 ≤ step d p x := by sorry
