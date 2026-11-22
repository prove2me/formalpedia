-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_exists_hole_tail_le_compressionLengthBoundIter
-- name    : DeciSigma1.Holes.Tail.exists_hole_tail_le_compressionLengthBoundIter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:59:38.413402+00:00
-- url     : https://prove2.me/theorems/08551c52-002d-4367-99d9-a17224196e67
-- title:
--   Tail: exists hole tail le compression Length Bound Iter
-- statement:
--   At most `n` passes bound every immortal rejected tail by
--   `compressionLengthBoundIter k N D n E`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Compression.lean#L567-L586
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Compression.lean#L567-L586

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

theorem DeciSigma1.Holes.Tail.exists_hole_tail_le_compressionLengthBoundIter (M : StructuralReader α S k) (D : ℕ)
    (n : ℕ) : ∀ (U : Fin k → List α) (E : ℕ),
    M.IsHole U → HasBoundedRunCover M U n D E →
    ∃ U', M.IsHole U' ∧ ∀ i, M.Immortal (M.endState U' i) → M.rejectedTailLength U' i ≤
      compressionLengthBoundIter k (Fintype.card S) D n E := by sorry
