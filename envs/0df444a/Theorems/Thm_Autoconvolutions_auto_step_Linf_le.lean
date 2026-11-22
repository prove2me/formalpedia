-- Prove2me | Theorems.Thm_Autoconvolutions_auto_step_Linf_le
-- name    : Autoconvolutions.auto_step_Linf_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:11.642606+00:00
-- url     : https://prove2.me/theorems/5d599127-b1ca-4b59-8558-ec96b0fe184f
-- title:
--   Autoconvolutions: auto step Linf le
-- statement:
--   An upper bound on every coefficient bounds the actual essential supremum.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Bounds.lean#L32-L52
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Bounds.lean#L32-L52

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

theorem Autoconvolutions.auto_step_Linf_le (d : ℕ) (p : Fin (d+1) → ℝ) (hp : ∀ i, 0 ≤ p i)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ k : ℤ, convCoeff d p k ≤ M) :
    (eLpNorm (auto (step d p)) ∞ volume).toReal ≤ M := by sorry
