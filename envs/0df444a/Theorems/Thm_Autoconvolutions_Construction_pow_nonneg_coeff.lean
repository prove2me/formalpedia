-- Prove2me | Theorems.Thm_Autoconvolutions_Construction_pow_nonneg_coeff
-- name    : Autoconvolutions.Construction.pow_nonneg_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:41.341729+00:00
-- url     : https://prove2.me/theorems/5f826738-c5b7-4eb2-b5ed-b0536afd21ab
-- title:
--   Construction: pow nonneg coeff
-- statement:
--   The Construction construction uses the pow nonneg coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Levels.lean#L94-L98
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Levels.lean#L94-L98

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

theorem Autoconvolutions.Construction.pow_nonneg_coeff {U : Polynomial ℝ} (hU : ∀ k, 0 ≤ U.coeff k) (n k : ℕ) :
    0 ≤ (U ^ n).coeff k := by sorry
