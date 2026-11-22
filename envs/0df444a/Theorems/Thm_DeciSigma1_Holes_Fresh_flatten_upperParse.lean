-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_flatten_upperParse
-- name    : DeciSigma1.Holes.Fresh.flatten_upperParse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:11.849626+00:00
-- url     : https://prove2.me/theorems/dce810ab-f844-47d4-884d-2faa221f99a8
-- title:
--   Fresh: flatten upper Parse
-- statement:
--   The Fresh construction uses the flatten upper Parse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L597-L602
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L597-L602

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

theorem DeciSigma1.Holes.Fresh.flatten_upperParse {t : ℕ} {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) :
    (upperParse W t o).flatten = occurrenceText W o := by sorry
