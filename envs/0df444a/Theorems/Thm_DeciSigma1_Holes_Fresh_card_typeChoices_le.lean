-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_card_typeChoices_le
-- name    : DeciSigma1.Holes.Fresh.card_typeChoices_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:35.102709+00:00
-- url     : https://prove2.me/theorems/467b14df-826e-4936-83aa-2d03c86095ba
-- title:
--   Fresh: card type Choices le
-- statement:
--   The Fresh construction uses the card type Choices le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L299-L305
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L299-L305

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}
variable {S : Type} [Fintype S] [DecidableEq S] {T : Table α S k}

theorem DeciSigma1.Holes.Fresh.card_typeChoices_le (W : Fin k → List α) (r : ℕ) :
    (typeChoices W r).card ≤ k + 1 := by sorry
