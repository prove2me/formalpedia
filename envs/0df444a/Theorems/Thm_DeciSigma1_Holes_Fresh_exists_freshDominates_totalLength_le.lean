-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_exists_freshDominates_totalLength_le
-- name    : DeciSigma1.Holes.Fresh.exists_freshDominates_totalLength_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:55.912444+00:00
-- url     : https://prove2.me/theorems/9cd21324-3bec-4c7d-8981-d481d152dffb
-- title:
--   Fresh: exists fresh Dominates total Length le
-- statement:
--   Every tuple of fresh words of a table with `k` starts and `N` states has a fresh dominator
--   of total length at most `freshTupleBound k N`: a minimal fresh dominator.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L986-L989
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L986-L989

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

theorem DeciSigma1.Holes.Fresh.exists_freshDominates_totalLength_le (hW : ∀ i, T.Fresh W i) :
    ∃ U, FreshDominates T U W ∧ totalLength U ≤ freshTupleBound k (Fintype.card S) := by sorry
