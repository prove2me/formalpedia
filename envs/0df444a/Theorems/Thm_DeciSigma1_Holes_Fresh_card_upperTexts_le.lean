-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_card_upperTexts_le
-- name    : DeciSigma1.Holes.Fresh.card_upperTexts_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:21.184543+00:00
-- url     : https://prove2.me/theorems/1f99372b-ee9e-4963-94da-b367e5d2695e
-- title:
--   Fresh: card upper Texts le
-- statement:
--   The number of distinct texts at one level is bounded by the number at the next level, the
--   number of parses of each, and the number of lower blocks in each parse.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L754-L765
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L754-L765

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

theorem DeciSigma1.Holes.Fresh.card_upperTexts_le (hsl : IsMinimalFresh T W) {t : ℕ} (ht : t + 1 ≤ topLevel W) :
    (upperTexts W t).card ≤ (upperParses W (t + 1)).card *
      (((upperParses W (t + 1)).card + 2) * edgeLengthBound k (Fintype.card S)) := by sorry
