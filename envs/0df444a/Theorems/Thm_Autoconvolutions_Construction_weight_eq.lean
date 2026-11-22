-- Prove2me | Theorems.Thm_Autoconvolutions_Construction_weight_eq
-- name    : Autoconvolutions.Construction.weight_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:54.156227+00:00
-- url     : https://prove2.me/theorems/e13a1caf-2ffb-41a0-b8f1-293c95494602
-- title:
--   Construction: weight eq
-- statement:
--   Geometric weights from the relative sizes of the two digit alphabets.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Levels.lean#L68-L73
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Levels.lean#L68-L73

module
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Real.Basic
public import Definitions.Def_Autoconvolutions_Levels
set_option autoImplicit true
@[expose] public section
public section
open Finset Polynomial
open scoped BigOperators
open Autoconvolutions Autoconvolutions.Construction

theorem Autoconvolutions.Construction.weight_eq (r b : ℝ) (hr : r ≠ 0) {m i : ℕ} (hi : i ≤ m) :
    r ^ (m - i) * b ^ (m + i) = (r * b) ^ m * (b / r) ^ i := by sorry
