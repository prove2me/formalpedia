-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_upperParse_eq_parseText
-- name    : DeciSigma1.Holes.Fresh.upperParse_eq_parseText
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:57.896543+00:00
-- url     : https://prove2.me/theorems/54d42821-7a36-4181-8bd1-2e9a85c15aab
-- title:
--   Fresh: upper Parse eq parse Text
-- statement:
--   The text of an upper occurrence and its lower anchors determine its parse.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L509-L531
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L509-L531

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

theorem DeciSigma1.Holes.Fresh.upperParse_eq_parseText {t : ℕ} {o : Fin k × ℕ × ℕ}
    (ho : o ∈ upperOccurrences W t) : upperParse W t o =
        parseText (occurrenceText W o) (occurrenceCuts W t o) := by sorry
