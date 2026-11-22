-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_site_spec
-- name    : DeciSigma1.Holes.Fresh.BlockDeletion.site_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:43:34.279721+00:00
-- url     : https://prove2.me/theorems/aaad678b-2cfd-4f5c-9afc-59c8dd7eb754
-- title:
--   Block Deletion: site spec
-- statement:
--   In a traversing occurrence `(l, s, e)`, the deletion site lies strictly inside the upper
--   block, its two cuts are lower anchors, and the deleted text has length `deletionLength`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L509-L530
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L509-L530

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

theorem DeciSigma1.Holes.Fresh.BlockDeletion.site_spec {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) (hth : m.edge.TraversedBy o) :
    o.2.1 < depthCut W t o m.maxDepth ∧ depthCut W t o m.maxDepth < depthCut W t o m.minDepth ∧
      depthCut W t o m.minDepth < o.2.2 ∧ o.2.2 ≤ (W o.1).length ∧
      depthCut W t o m.maxDepth + m.deletionLength = depthCut W t o m.minDepth ∧
      depthCut W t o m.maxDepth ∈ anchors W t o.1 ∧ depthCut W t o m.minDepth ∈
          anchors W t o.1 := by sorry
