-- Prove2me | Theorems.Thm_Autoconvolutions_auto_step_Linf_pos
-- name    : Autoconvolutions.auto_step_Linf_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:15.106256+00:00
-- url     : https://prove2.me/theorems/a3a9c221-bc96-4aab-b882-b894fd1ec17b
-- title:
--   Autoconvolutions: auto step Linf pos
-- statement:
--   The Autoconvolutions construction uses the auto step Linf pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Bounds.lean#L54-L59
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Bounds.lean#L54-L59

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

theorem Autoconvolutions.auto_step_Linf_pos {d : ℕ} {p : Fin (d+1) → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hne : ∃ i, 0 < p i) :
    0 < (eLpNorm (auto (step d p)) ∞ volume).toReal := by sorry
