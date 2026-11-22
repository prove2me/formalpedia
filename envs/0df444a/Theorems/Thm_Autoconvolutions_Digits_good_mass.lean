-- Prove2me | Theorems.Thm_Autoconvolutions_Digits_good_mass
-- name    : Autoconvolutions.Digits.good_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:30.26712+00:00
-- url     : https://prove2.me/theorems/67ed9a50-e1cb-4703-afd2-11b5d8948ca7
-- title:
--   Digits: good mass
-- statement:
--   Algebraic form of equation (mass), including its factorial and binomial
--   factors. Neither side involves floating-point arithmetic.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Digits.lean#L123-L138
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Digits.lean#L123-L138

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

theorem Autoconvolutions.Digits.good_mass {r b n u v : ℕ} (hn : 0 < n) (hb : 8*n^3 ≤ b)
    (hbr : b ≤ r) (huv : u + v = 4*n) :
    (1-1/(n : ℝ))*((r : ℝ)^u*(b : ℝ)^v) ≤
      (r.choose u : ℝ)*(b.choose v : ℝ)*(u.factorial : ℝ)*(v.factorial : ℝ) := by sorry
