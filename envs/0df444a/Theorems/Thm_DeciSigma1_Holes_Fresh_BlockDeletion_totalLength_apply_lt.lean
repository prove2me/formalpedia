-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_totalLength_apply_lt
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.totalLength_apply_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:08.809859+00:00
-- url     : https://prove2.me/theorems/cddee024-37cb-4278-9277-c8a5e9c9259b
-- title:
--   Block Deletion: total Length apply lt
-- statement:
--   The edited tuple is shorter.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L641-L654
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L641-L654

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.totalLength_apply_lt : totalLength m.apply < totalLength W := by sorry
