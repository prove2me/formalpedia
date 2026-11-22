-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_runPrefix_apply
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.runPrefix_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:11.870175+00:00
-- url     : https://prove2.me/theorems/e2d7866a-3649-4688-a513-44170837a5e9
-- title:
--   Block Deletion: run Prefix apply
-- statement:
--   The state of an edited word at a cut is the state of the original word at the greatest
--   preimage of the cut.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L605-L609
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L605-L609

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.runPrefix_apply (l : Fin k) (a : ℕ) :
    T.runPrefix m.apply l a =
      T.runPrefix W l (greatestPreimage (sitePositions m.deletionLength (m.sites l)) a) := by sorry
