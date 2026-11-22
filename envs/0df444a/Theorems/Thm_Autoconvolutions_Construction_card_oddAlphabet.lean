-- Prove2me | Theorems.Thm_Autoconvolutions_Construction_card_oddAlphabet
-- name    : Autoconvolutions.Construction.card_oddAlphabet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:08.530112+00:00
-- url     : https://prove2.me/theorems/a5e52fa8-ca32-4719-b9f9-1b90e9840ccd
-- title:
--   Construction: card odd Alphabet
-- statement:
--   The Construction construction uses the card odd Alphabet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Levels.lean#L127-L127
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Levels.lean#L127-L127

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

theorem Autoconvolutions.Construction.card_oddAlphabet (r : ℕ) : (oddAlphabet r).card = r := by sorry
