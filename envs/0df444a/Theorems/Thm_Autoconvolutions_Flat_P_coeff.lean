-- Prove2me | Theorems.Thm_Autoconvolutions_Flat_P_coeff
-- name    : Autoconvolutions.Flat.P_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:10.687662+00:00
-- url     : https://prove2.me/theorems/b3a1d91d-f73b-479c-8d1b-00803e2b708c
-- title:
--   Flat: P coeff
-- statement:
--   The Flat construction uses the P coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Flat.lean#L124-L127
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Flat.lean#L124-L127

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

theorem Autoconvolutions.Flat.P_coeff (i h : ℕ) :
    (P i).coeff h = if h ≤ i then weight h * weight (i-h) else 0 := by sorry
