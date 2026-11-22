-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_compressionLengthBoundIter_le_affine
-- name    : DeciSigma1.Holes.Tail.compressionLengthBoundIter_le_affine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:58:15.078124+00:00
-- url     : https://prove2.me/theorems/37ebb185-8fc3-4ac2-88a3-bb2b479233d2
-- title:
--   Tail: compression Length Bound Iter le affine
-- statement:
--   A common affine envelope for the descending compression passes, including zero runs.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ElementaryBound.lean#L73-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ElementaryBound.lean#L73-L118

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Compression
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ElementaryBound
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open Arithmetic

theorem DeciSigma1.Holes.Tail.compressionLengthBoundIter_le_affine (k N D r E : ℕ) :
    compressionLengthBoundIter k N D r E ≤
      (1 + r * compressionSlope k N D) ^ r *
        (E + r * compressionIntercept k N D r) := by sorry
