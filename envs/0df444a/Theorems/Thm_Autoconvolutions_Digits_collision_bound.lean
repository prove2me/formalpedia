-- Prove2me | Theorems.Thm_Autoconvolutions_Digits_collision_bound
-- name    : Autoconvolutions.Digits.collision_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:25.771407+00:00
-- url     : https://prove2.me/theorems/48312dc7-c631-4439-8e06-efc54954b7a5
-- title:
--   Digits: collision bound
-- statement:
--   Twice the alphabet size times the collision probability is at most k².
--   The sharp intermediate bound k(k-1) is unnecessary for the final constant.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Digits.lean#L79-L88
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Digits.lean#L79-L88

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

theorem Autoconvolutions.Digits.collision_bound {r : ℕ} (hr : 0 < r) (k : ℕ) :
    2 * (r : ℝ) * (1 - distinctFraction r k) ≤ (k : ℝ)^2 := by sorry
