-- Prove2me | Theorems.Thm_Autoconvolutions_Flat_B_coeff_nonneg
-- name    : Autoconvolutions.Flat.B_coeff_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:13.428691+00:00
-- url     : https://prove2.me/theorems/1f4e0ad1-37c3-4186-8a65-17db68eb79a2
-- title:
--   Flat: B coeff nonneg
-- statement:
--   The Flat construction uses the B coeff nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Flat.lean#L170-L172
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Flat.lean#L170-L172

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

theorem Autoconvolutions.Flat.B_coeff_nonneg (K s h : ℕ) : 0 ≤ (B K s).coeff h := by sorry
