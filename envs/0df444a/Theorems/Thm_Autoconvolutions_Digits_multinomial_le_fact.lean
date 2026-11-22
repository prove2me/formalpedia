-- Prove2me | Theorems.Thm_Autoconvolutions_Digits_multinomial_le_fact
-- name    : Autoconvolutions.Digits.multinomial_le_fact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:19.265995+00:00
-- url     : https://prove2.me/theorems/95624d95-cf18-473b-a0fd-241bb5155b78
-- title:
--   Digits: multinomial le fact
-- statement:
--   A bound independent of the multiplicities, including repeated choices.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Digits.lean#L25-L27
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Digits.lean#L25-L27

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

theorem Autoconvolutions.Digits.multinomial_le_fact {ι : Type*} (I : Finset ι) (a : ι → ℕ) :
    Nat.multinomial I a ≤ (∑ i ∈ I, a i).factorial := by sorry
