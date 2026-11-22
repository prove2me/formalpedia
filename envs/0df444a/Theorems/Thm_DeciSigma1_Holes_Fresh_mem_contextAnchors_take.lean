-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_mem_contextAnchors_take
-- name    : DeciSigma1.Holes.Fresh.mem_contextAnchors_take
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:03.357583+00:00
-- url     : https://prove2.me/theorems/74826ee4-b01f-498f-9110-638b19634bdb
-- title:
--   Fresh: mem context Anchors take
-- statement:
--   The Fresh construction uses the mem context Anchors take property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L533-L537
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L533-L537

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

theorem DeciSigma1.Holes.Fresh.mem_contextAnchors_take {t : ℕ} {u : List α} {e p : ℕ} (hp : p ≤ min e u.length) :
    p ∈ contextAnchors W t (u.take e) ↔ p ∈ contextAnchors W t u := by sorry
