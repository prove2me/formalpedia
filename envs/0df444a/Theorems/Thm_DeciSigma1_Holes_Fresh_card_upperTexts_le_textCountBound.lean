-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_card_upperTexts_le_textCountBound
-- name    : DeciSigma1.Holes.Fresh.card_upperTexts_le_textCountBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:39.050429+00:00
-- url     : https://prove2.me/theorems/390463a1-2968-4d43-9cbc-caacc5fe9df0
-- title:
--   Fresh: card upper Texts le text Count Bound
-- statement:
--   The Fresh construction uses the card upper Texts le text Count Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L861-L865
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L861-L865

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

theorem DeciSigma1.Holes.Fresh.card_upperTexts_le_textCountBound (hsl : IsMinimalFresh T W) {t : ℕ} (ht : t ≤ topLevel W) :
    (upperTexts W t).card ≤ textCountBound k (Fintype.card S) := by sorry
