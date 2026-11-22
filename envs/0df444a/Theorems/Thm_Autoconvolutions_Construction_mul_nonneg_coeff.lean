-- Prove2me | Theorems.Thm_Autoconvolutions_Construction_mul_nonneg_coeff
-- name    : Autoconvolutions.Construction.mul_nonneg_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:11.130415+00:00
-- url     : https://prove2.me/theorems/bc761b36-01e4-4b73-9976-234d718b3f57
-- title:
--   Construction: mul nonneg coeff
-- statement:
--   Coefficientwise nonnegativity is preserved under multiplication.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Levels.lean#L88-L92
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Levels.lean#L88-L92

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

theorem Autoconvolutions.Construction.mul_nonneg_coeff {U V : Polynomial ℝ}
    (hU : ∀ k, 0 ≤ U.coeff k) (hV : ∀ k, 0 ≤ V.coeff k) (k : ℕ) :
    0 ≤ (U * V).coeff k := by sorry
