-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_card_prefixOccurrenceCuts_le
-- name    : DeciSigma1.Holes.Fresh.card_prefixOccurrenceCuts_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:02.004809+00:00
-- url     : https://prove2.me/theorems/d2f61da6-5f00-4e40-aa9d-3a4562ede77d
-- title:
--   Fresh: card prefix Occurrence Cuts le
-- statement:
--   The Fresh construction uses the card prefix Occurrence Cuts le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L791-L803
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L791-L803

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

theorem DeciSigma1.Holes.Fresh.card_prefixOccurrenceCuts_le {T : Table α S k} {W : Fin k → List α} (hfr : ∀ i, T.Fresh W i)
    (z : List α) : (prefixOccurrenceCuts W z).card ≤ k * (Fintype.card S - 1) := by sorry
