-- Prove2me | Theorems.Thm_Autoconvolutions_Digits_good_fraction
-- name    : Autoconvolutions.Digits.good_fraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:30.358809+00:00
-- url     : https://prove2.me/theorems/84948245-91b9-454c-9298-2b65a8edbfaa
-- title:
--   Digits: good fraction
-- statement:
--   The paper's good-block estimate, with the numbers of draws named u,v.
--   At level s use u=2n-s, v=2n+s.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Digits.lean#L92-L119
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Digits.lean#L92-L119

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

theorem Autoconvolutions.Digits.good_fraction {r b n u v : ℕ} (hn : 0 < n) (hb : 8*n^3 ≤ b)
    (hbr : b ≤ r) (huv : u + v = 4*n) :
    1 - 1/(n : ℝ) ≤ distinctFraction r u * distinctFraction b v := by sorry
