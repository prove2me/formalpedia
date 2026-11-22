-- Prove2me | Theorems.Thm_Autoconvolutions_Digits_distinctFraction_nonneg
-- name    : Autoconvolutions.Digits.distinctFraction_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:21.60807+00:00
-- url     : https://prove2.me/theorems/33b79c42-ac65-4422-b74f-51b795baab5d
-- title:
--   Digits: distinct Fraction nonneg
-- statement:
--   The Digits construction uses the distinct Fraction nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Digits.lean#L43-L45
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Digits.lean#L43-L45

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

theorem Autoconvolutions.Digits.distinctFraction_nonneg (r k : ℕ) : 0 ≤ distinctFraction r k := by sorry
