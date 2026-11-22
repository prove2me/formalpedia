-- Prove2me | Theorems.Thm_Autoconvolutions_Construction_disjoint_alphabets
-- name    : Autoconvolutions.Construction.disjoint_alphabets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:45.705748+00:00
-- url     : https://prove2.me/theorems/38a37370-09e1-42fa-b7e1-bf85eb4f19a0
-- title:
--   Construction: disjoint alphabets
-- statement:
--   The Construction construction uses the disjoint alphabets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Levels.lean#L132-L140
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Levels.lean#L132-L140

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

theorem Autoconvolutions.Construction.disjoint_alphabets (r b : ℕ) (hb : b ≤ r) :
    Disjoint (oddAlphabet r) (evenAlphabet r b hb) := by sorry
