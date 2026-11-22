-- Prove2me | Theorems.Thm_Autoconvolutions_auto_step_L2_sq
-- name    : Autoconvolutions.auto_step_L2_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:11.558742+00:00
-- url     : https://prove2.me/theorems/28904192-809f-40d8-a577-650a172afb5f
-- title:
--   Autoconvolutions: auto step L2 sq
-- statement:
--   The Autoconvolutions construction uses the auto step L2 sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Bounds.lean#L24-L29
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Bounds.lean#L24-L29

module
public import Definitions.Def_Autoconvolutions_Step
public import Definitions.Def_Autoconvolutions_Interpolation
public import Mathlib.MeasureTheory.Function.L2Space
public import Definitions.Def_Autoconvolutions_Bounds
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators
open Autoconvolutions

theorem Autoconvolutions.auto_step_L2_sq (d : ℕ) (p : Fin (d+1) → ℝ) :
    (eLpNorm (auto (step d p)) 2 volume).toReal^2 = ∫ x, auto (step d p) x ^ 2 := by sorry
