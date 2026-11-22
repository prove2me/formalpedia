-- Prove2me | Theorems.Thm_Autoconvolutions_Construction_family_sq
-- name    : Autoconvolutions.Construction.family_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:55.106022+00:00
-- url     : https://prove2.me/theorems/d4d9befc-6717-409f-a1c6-22f1b662e7d2
-- title:
--   Construction: family sq
-- statement:
--   Group the ordered pairs in the square by the sum of their two levels.
--   All subtractions are in ℕ. The bound K ≤ n is what makes the power identity valid.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Levels.lean#L33-L65
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Levels.lean#L33-L65

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

theorem Autoconvolutions.Construction.family_sq (P : ℕ → Polynomial ℝ) (U V : Polynomial ℝ) {n K : ℕ} (hK : K ≤ n) :
    family P U V n K ^ 2 = ∑ s ∈ range (2 * K + 1), level U V n s * block P K s := by sorry
