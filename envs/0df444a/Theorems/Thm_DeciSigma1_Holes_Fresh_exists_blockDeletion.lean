-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_exists_blockDeletion
-- name    : DeciSigma1.Holes.Fresh.exists_blockDeletion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:48.107374+00:00
-- url     : https://prove2.me/theorems/497ad18b-0670-4bfc-8834-f2795ff37b3d
-- title:
--   Fresh: exists block Deletion
-- statement:
--   An edge longer than `edgeLengthBound` admits a block deletion: by the pigeonhole principle
--   two depths carry the same joint label.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L360-L397
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L360-L397

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

theorem DeciSigma1.Holes.Fresh.exists_blockDeletion (hfr : ∀ i, T.Fresh W i)
    {t : ℕ} (ht : t ≤ k * Fintype.card S + 1) (e : Edge W t)
    (hlong : edgeLengthBound k (Fintype.card S) < e.endDepth - e.startDepth) : Nonempty
        (BlockDeletion T W t) := by sorry
