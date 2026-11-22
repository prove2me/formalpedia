-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_not_exists_blockDeletion_of_minimalFresh
-- name    : DeciSigma1.Holes.Fresh.not_exists_blockDeletion_of_minimalFresh
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:51.022302+00:00
-- url     : https://prove2.me/theorems/dc4200fa-166d-4531-b2d4-c244cae8d473
-- title:
--   Fresh: not exists block Deletion of minimal Fresh
-- statement:
--   A minimal fresh tuple admits no block deletion: the edited tuple would be a shorter fresh
--   dominator.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L403-L406
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L403-L406

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

theorem DeciSigma1.Holes.Fresh.not_exists_blockDeletion_of_minimalFresh (hsl : IsMinimalFresh T W)
    {t : ℕ} : ¬ Nonempty (BlockDeletion T W t) := by sorry
