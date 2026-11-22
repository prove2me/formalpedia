-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_take_start_append_occurrenceText
-- name    : DeciSigma1.Holes.Fresh.take_start_append_occurrenceText
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:42.799844+00:00
-- url     : https://prove2.me/theorems/b9fc5cde-38e0-436a-843e-e58de2970d0f
-- title:
--   Fresh: take start append occurrence Text
-- statement:
--   The Fresh construction uses the take start append occurrence Text property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L502-L506
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L502-L506

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

theorem DeciSigma1.Holes.Fresh.take_start_append_occurrenceText {t : ℕ} {o : Fin k × ℕ × ℕ}
    (ho : o ∈ upperOccurrences W t) : (W o.1).take o.2.1 ++ occurrenceText W o =
        (W o.1).take o.2.2 := by sorry
