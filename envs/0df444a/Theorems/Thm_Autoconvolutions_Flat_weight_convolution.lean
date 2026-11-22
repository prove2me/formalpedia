-- Prove2me | Theorems.Thm_Autoconvolutions_Flat_weight_convolution
-- name    : Autoconvolutions.Flat.weight_convolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:13.736355+00:00
-- url     : https://prove2.me/theorems/5eca0874-ca84-4494-b99f-34096c6fed5b
-- title:
--   Flat: weight convolution
-- statement:
--   The normalized central-binomial convolution.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Flat.lean#L49-L84
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Flat.lean#L49-L84

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

theorem Autoconvolutions.Flat.weight_convolution (n : ℕ) :
    ∑ p ∈ antidiagonal n, weight p.1 * weight p.2 = 1 := by sorry
