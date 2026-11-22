-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_freshDominates_of_channel
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.freshDominates_of_channel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:08.546154+00:00
-- url     : https://prove2.me/theorems/9beda2e2-b3c2-4040-873b-85c28abf2d3a
-- title:
--   Block Deletion: fresh Dominates of channel
-- statement:
--   A block deletion whose edited tuple has smaller channels is a fresh domination.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L666-L668
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L666-L668

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
variable {S : Type} [Fintype S]
open DeciSigma1.Holes.Fresh.BlockDeletion
variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)

theorem DeciSigma1.Holes.Fresh.BlockDeletion.freshDominates_of_channel [DecidableEq S] (hfr : ∀ i, T.Fresh W i)
    (hch : ∀ i j, T.channel m.apply i j ⊆ T.channel W i j) : FreshDominates T m.apply W := by sorry
