-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_upperParse_length_le
-- name    : DeciSigma1.Holes.Fresh.upperParse_length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:42.06958+00:00
-- url     : https://prove2.me/theorems/edd6b5e7-9b2f-41ca-a693-27b5a2f68acc
-- title:
--   Fresh: upper Parse length le
-- statement:
--   The parse of an upper block of a minimal fresh tuple has a bounded number of lower blocks:
--   its path in the reverse trie has few nodes, and every edge is short.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L667-L679
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L667-L679

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

theorem DeciSigma1.Holes.Fresh.upperParse_length_le (hsl : IsMinimalFresh T W) {t : ℕ} (ht : t ≤ topLevel W)
    {Z : List (List α)} (hZ : Z ∈ upperParses W t) :
    Z.length ≤ ((upperParses W t).card + 2) * edgeLengthBound k (Fintype.card S) := by sorry
