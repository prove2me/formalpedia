-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_exists_hole_tail_le_compressionLengthBound
-- name    : DeciSigma1.Holes.Tail.exists_hole_tail_le_compressionLengthBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:00:01.162968+00:00
-- url     : https://prove2.me/theorems/311d5420-c6ba-4a58-80b5-1e60d6054640
-- title:
--   Tail: exists hole tail le compression Length Bound
-- statement:
--   A hole with a run cover has a hole whose immortal rejected tails have at most
--   `compressionLengthBound k N R D E` letters.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Compression.lean#L590-L594
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Compression.lean#L590-L594

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Bound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RunCovers
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Compression
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
variable [DecidableEq α] [Fintype S] [DecidableEq S]

theorem DeciSigma1.Holes.Tail.exists_hole_tail_le_compressionLengthBound (M : StructuralReader α S k) {W : Fin k → List α}
    (hW : M.IsHole W) {R D E : ℕ} (hcov : HasScaledRunCover M W R D E) :
    ∃ W', M.IsHole W' ∧ ∀ i, M.Immortal (M.endState W' i) → M.rejectedTailLength W' i ≤
      compressionLengthBound k (Fintype.card S) R D E := by sorry
