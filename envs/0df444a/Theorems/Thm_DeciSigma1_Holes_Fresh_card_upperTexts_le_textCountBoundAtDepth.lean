-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_card_upperTexts_le_textCountBoundAtDepth
-- name    : DeciSigma1.Holes.Fresh.card_upperTexts_le_textCountBoundAtDepth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:35.042437+00:00
-- url     : https://prove2.me/theorems/55084603-c123-4412-a8bf-30f4a5fe52e8
-- title:
--   Fresh: card upper Texts le text Count Bound At Depth
-- statement:
--   The number of distinct texts `d` levels below the top is at most
--   `textCountBoundAtDepth k N d`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L839-L859
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L839-L859

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

theorem DeciSigma1.Holes.Fresh.card_upperTexts_le_textCountBoundAtDepth (hsl : IsMinimalFresh T W) (d : ℕ) :
    ∀ t, t + d = topLevel W → (upperTexts W t).card ≤
        textCountBoundAtDepth k (Fintype.card S) d := by sorry
