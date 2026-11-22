-- Prove2me | Theorems.Thm_Autoconvolutions_Digits_distinctFraction_le_one
-- name    : Autoconvolutions.Digits.distinctFraction_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:46.538749+00:00
-- url     : https://prove2.me/theorems/b284c9d8-d429-4823-891b-032b4e20d3ab
-- title:
--   Digits: distinct Fraction le one
-- statement:
--   The Digits construction uses the distinct Fraction le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Digits.lean#L47-L52
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Digits.lean#L47-L52

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

theorem Autoconvolutions.Digits.distinctFraction_le_one {r : ℕ} (hr : 0 < r) (k : ℕ) :
    distinctFraction r k ≤ 1 := by sorry
