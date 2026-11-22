-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_fresh_apply
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.fresh_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:07.950154+00:00
-- url     : https://prove2.me/theorems/13d8802f-07f9-4881-b276-90b69d24d1aa
-- title:
--   Block Deletion: fresh apply
-- statement:
--   The edited tuple is fresh.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L634-L638
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L634-L638

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.fresh_apply [DecidableEq S] (hfr : ∀ i, T.Fresh W i) (l : Fin k) :
    T.Fresh m.apply l := by sorry
