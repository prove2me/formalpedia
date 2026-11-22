-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_le_compressionLengthBoundIter
-- name    : DeciSigma1.Holes.Tail.le_compressionLengthBoundIter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:59:43.480324+00:00
-- url     : https://prove2.me/theorems/7c0d44ff-94c2-477b-ab98-5ceeb96df5a1
-- title:
--   Tail: le compression Length Bound Iter
-- statement:
--   The Tail construction uses the le compression Length Bound Iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Compression.lean#L553-L555
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Compression.lean#L553-L555

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

theorem DeciSigma1.Holes.Tail.le_compressionLengthBoundIter (k N D : ℕ) : ∀ n E, E ≤ compressionLengthBoundIter k N D n E
  := by sorry
