-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_edge_length_le
-- name    : DeciSigma1.Holes.Fresh.edge_length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:54.753475+00:00
-- url     : https://prove2.me/theorems/1e934795-2469-482b-b05d-91a866466c93
-- title:
--   Fresh: edge length le
-- statement:
--   Every edge of the reverse trie of a minimal fresh tuple at a level up to the top level has
--   length at most `edgeLengthBound k N`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L410-L416
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L410-L416

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

theorem DeciSigma1.Holes.Fresh.edge_length_le (hsl : IsMinimalFresh T W) {t : ℕ} (ht : t ≤ topLevel W) (e : Edge W t) :
    e.endDepth - e.startDepth ≤ edgeLengthBound k (Fintype.card S) := by sorry
