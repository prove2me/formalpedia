-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_endState_apply
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.endState_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:54:47.759213+00:00
-- url     : https://prove2.me/theorems/c45c3523-a405-42d1-8828-a38576350538
-- title:
--   Block Deletion: end State apply
-- statement:
--   The edited tuple has the same endpoints.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L612-L615
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L612-L615

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.endState_apply (l : Fin k) :
    T.endState m.apply l = T.endState W l := by sorry
