-- Prove2me | Theorems.Thm_Autoconvolutions_Construction_family_nonneg_coeff
-- name    : Autoconvolutions.Construction.family_nonneg_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:41.097482+00:00
-- url     : https://prove2.me/theorems/f4515e5e-c1c7-46de-bba5-539e83f91733
-- title:
--   Construction: family nonneg coeff
-- statement:
--   The Construction construction uses the family nonneg coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Levels.lean#L100-L106
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Levels.lean#L100-L106

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

theorem Autoconvolutions.Construction.family_nonneg_coeff (P : ℕ → Polynomial ℝ) {U V : Polynomial ℝ}
    (hP : ∀ i k, 0 ≤ (P i).coeff k) (hU : ∀ k, 0 ≤ U.coeff k)
    (hV : ∀ k, 0 ≤ V.coeff k) (n K k : ℕ) : 0 ≤ (family P U V n K).coeff k := by sorry
