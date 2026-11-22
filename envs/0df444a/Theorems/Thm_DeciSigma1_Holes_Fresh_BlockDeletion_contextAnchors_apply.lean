-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_contextAnchors_apply
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.contextAnchors_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:54:51.249358+00:00
-- url     : https://prove2.me/theorems/d2e6108e-19d1-4a6a-9421-209ea8fe8934
-- title:
--   Block Deletion: context Anchors apply
-- statement:
--   For the markers of `W`, the level-`r` anchors (`1 ≤ r ≤ t + 1`) of an edited word are exactly
--   the images under the cut map of the original anchors that are not deleted.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L658-L663
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L658-L663

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.contextAnchors_apply {r : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ t + 1) (l : Fin k) (e' : ℕ) :
    e' ∈ contextAnchors W r (m.apply l) ↔
      ∃ p ∈ contextAnchors W r (W l), Retained m.deletionLength (m.sites l) p ∧
        retainedCount (sitePositions m.deletionLength (m.sites l)) p = e' := by sorry
