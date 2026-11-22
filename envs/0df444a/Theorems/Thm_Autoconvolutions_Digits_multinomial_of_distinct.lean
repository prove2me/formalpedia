-- Prove2me | Theorems.Thm_Autoconvolutions_Digits_multinomial_of_distinct
-- name    : Autoconvolutions.Digits.multinomial_of_distinct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:21.534829+00:00
-- url     : https://prove2.me/theorems/68914931-fbc2-4f89-ae14-3e6071065537
-- title:
--   Digits: multinomial of distinct
-- statement:
--   If every occupied digit was chosen only once, the bound is attained.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Digits.lean#L30-L37
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Digits.lean#L30-L37

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

theorem Autoconvolutions.Digits.multinomial_of_distinct {ι : Type*} (I : Finset ι) (a : ι → ℕ)
    (ha : ∀ i ∈ I, a i ≤ 1) :
    Nat.multinomial I a = (∑ i ∈ I, a i).factorial := by sorry
