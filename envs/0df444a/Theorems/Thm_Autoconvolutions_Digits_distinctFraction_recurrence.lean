-- Prove2me | Theorems.Thm_Autoconvolutions_Digits_distinctFraction_recurrence
-- name    : Autoconvolutions.Digits.distinctFraction_recurrence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:26.616114+00:00
-- url     : https://prove2.me/theorems/e7e0f970-7f66-4ec8-9bee-149bf47e06c4
-- title:
--   Digits: distinct Fraction recurrence
-- statement:
--   Extending a distinct string of length k has exactly r-k available choices.
--   The equality also holds when k exceeds the alphabet size.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Digits.lean#L56-L75
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Digits.lean#L56-L75

module
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_Autoconvolutions_Digits
set_option autoImplicit true
@[expose] public section
public section
open Autoconvolutions Autoconvolutions.Digits

theorem Autoconvolutions.Digits.distinctFraction_recurrence {r : ℕ} (hr : 0 < r) (k : ℕ) :
    (r : ℝ) * distinctFraction r k =
      (r : ℝ) * distinctFraction r (k + 1) + (k : ℝ) * distinctFraction r k := by sorry
