-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_occurrenceCuts_eq
-- name    : DeciSigma1.Holes.Fresh.occurrenceCuts_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:07.376826+00:00
-- url     : https://prove2.me/theorems/6be49ca0-5ca9-4ce0-84f1-1f36b166f1ca
-- title:
--   Fresh: occurrence Cuts eq
-- statement:
--   The lower anchors of an upper occurrence are its end and the anchors of its text in its
--   left context.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L541-L565
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L541-L565

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

theorem DeciSigma1.Holes.Fresh.occurrenceCuts_eq {t : ℕ} {o : Fin k × ℕ × ℕ}
    (ho : o ∈ upperOccurrences W t) : occurrenceCuts W t o =
      insert (occurrenceText W o).length
          (relativeAnchors W t ((W o.1).take o.2.1) (occurrenceText W o)) := by sorry
