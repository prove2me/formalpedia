-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_card_suffixOccurrenceCuts_le
-- name    : DeciSigma1.Holes.Fresh.card_suffixOccurrenceCuts_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:49.629596+00:00
-- url     : https://prove2.me/theorems/155b8693-6a1b-4faa-a66a-ec80d3cc2437
-- title:
--   Fresh: card suffix Occurrence Cuts le
-- statement:
--   The Fresh construction uses the card suffix Occurrence Cuts le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L768-L770
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L768-L770

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
variable [DecidableEq α]
open DeciSigma1.Readers.Table
variable {S : Type} [Fintype S] [DecidableEq S]

theorem DeciSigma1.Holes.Fresh.card_suffixOccurrenceCuts_le {T : Table α S k} {W : Fin k → List α} (hfr : ∀ i, T.Fresh W i)
    (j : Fin k) (z : List α) : (suffixOccurrenceCuts W j z).card ≤ Fintype.card S - 1 := by sorry
