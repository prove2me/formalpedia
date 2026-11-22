-- Prove2me | Theorems.Thm_Autoconvolutions_Flat_weight_pos
-- name    : Autoconvolutions.Flat.weight_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:56.113525+00:00
-- url     : https://prove2.me/theorems/087f07c5-f255-4fad-8553-f79d02a1f969
-- title:
--   Flat: weight pos
-- statement:
--   The Flat construction uses the weight pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Flat.lean#L35-L36
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Flat.lean#L35-L36

module
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Definitions.Def_Autoconvolutions_Flat
set_option autoImplicit true
@[expose] public section
public section
open Finset Polynomial
open Autoconvolutions Autoconvolutions.Flat
noncomputable section

theorem Autoconvolutions.Flat.weight_pos (n : ℕ) : 0 < weight n := by sorry
