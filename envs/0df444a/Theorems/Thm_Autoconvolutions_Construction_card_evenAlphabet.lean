-- Prove2me | Theorems.Thm_Autoconvolutions_Construction_card_evenAlphabet
-- name    : Autoconvolutions.Construction.card_evenAlphabet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:08.015416+00:00
-- url     : https://prove2.me/theorems/80ab376d-f93a-4984-8831-9ba71bb811da
-- title:
--   Construction: card even Alphabet
-- statement:
--   The Construction construction uses the card even Alphabet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Levels.lean#L129-L130
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Levels.lean#L129-L130

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

theorem Autoconvolutions.Construction.card_evenAlphabet (r b : ℕ) (hb : b ≤ r) : (evenAlphabet r b hb).card = b := by sorry
