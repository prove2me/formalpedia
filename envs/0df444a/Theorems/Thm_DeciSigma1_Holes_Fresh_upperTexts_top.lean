-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_upperTexts_top
-- name    : DeciSigma1.Holes.Fresh.upperTexts_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:42.627274+00:00
-- url     : https://prove2.me/theorems/284c3fec-34bc-4dc2-a2cd-622948859faa
-- title:
--   Fresh: upper Texts top
-- statement:
--   The Fresh construction uses the upper Texts top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L822-L830
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L822-L830

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

theorem DeciSigma1.Holes.Fresh.upperTexts_top :
    upperTexts W (topLevel W) = (univ.filter fun l => W l ≠ []).image W := by sorry
