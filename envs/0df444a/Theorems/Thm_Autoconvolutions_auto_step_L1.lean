-- Prove2me | Theorems.Thm_Autoconvolutions_auto_step_L1
-- name    : Autoconvolutions.auto_step_L1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:10.649516+00:00
-- url     : https://prove2.me/theorems/ba87b5b7-162b-4954-bd5c-7e64df059144
-- title:
--   Autoconvolutions: auto step L1
-- statement:
--   The Autoconvolutions construction uses the auto step L1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Bounds.lean#L18-L22
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Bounds.lean#L18-L22

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

theorem Autoconvolutions.auto_step_L1 (d : ℕ) (p : Fin (d+1) → ℝ) (hp : ∀ i, 0 ≤ p i) :
    (eLpNorm (auto (step d p)) 1 volume).toReal = (∑ i, p i)^2 := by sorry
