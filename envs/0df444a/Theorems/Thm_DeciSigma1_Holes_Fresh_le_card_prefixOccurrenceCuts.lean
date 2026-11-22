-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_le_card_prefixOccurrenceCuts
-- name    : DeciSigma1.Holes.Fresh.le_card_prefixOccurrenceCuts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:54.393648+00:00
-- url     : https://prove2.me/theorems/2287a946-63b1-48c9-861e-a655f1b7461c
-- title:
--   Fresh: le card prefix Occurrence Cuts
-- statement:
--   The Fresh construction uses the le card prefix Occurrence Cuts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L805-L835
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L805-L835

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

theorem DeciSigma1.Holes.Fresh.le_card_prefixOccurrenceCuts {W : Fin k → List α} {t : ℕ} (ht : 1 ≤ t) :
    ∀ l ∈ active W t, t ≤ (prefixOccurrenceCuts W (marker W t l)).card := by sorry
