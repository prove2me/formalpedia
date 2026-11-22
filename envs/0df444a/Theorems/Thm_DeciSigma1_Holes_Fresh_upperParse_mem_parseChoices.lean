-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_upperParse_mem_parseChoices
-- name    : DeciSigma1.Holes.Fresh.upperParse_mem_parseChoices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:06.942657+00:00
-- url     : https://prove2.me/theorems/4b5e0902-0118-47b9-82f0-90acef5d5db1
-- title:
--   Fresh: upper Parse mem parse Choices
-- statement:
--   The parse of every upper occurrence is one of the candidates for its text.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L574-L587
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L574-L587

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

theorem DeciSigma1.Holes.Fresh.upperParse_mem_parseChoices {t : ℕ} {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) :
    upperParse W t o ∈ parseChoices W t (occurrenceText W o) := by sorry
