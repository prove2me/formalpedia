-- Prove2me | Theorems.Thm_Autoconvolutions_Construction_eval_family_one
-- name    : Autoconvolutions.Construction.eval_family_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:36.525479+00:00
-- url     : https://prove2.me/theorems/53a67f9e-eafc-477a-b869-6be35e04ff54
-- title:
--   Construction: eval family one
-- statement:
--   The Construction construction uses the eval family one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Levels.lean#L75-L85
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Levels.lean#L75-L85

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

theorem Autoconvolutions.Construction.eval_family_one (P : ℕ → Polynomial ℝ) (U V : Polynomial ℝ) {n K : ℕ}
    (hK : K ≤ n) (hP : ∀ i, (P i).eval 1 = 1) (hU : U.eval 1 ≠ 0) :
    (family P U V n K).eval 1 =
      (U.eval 1 * V.eval 1) ^ n * ∑ i ∈ range (K + 1), (V.eval 1 / U.eval 1) ^ i := by sorry
