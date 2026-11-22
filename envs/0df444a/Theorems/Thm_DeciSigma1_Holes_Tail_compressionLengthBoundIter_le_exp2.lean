-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_compressionLengthBoundIter_le_exp2
-- name    : DeciSigma1.Holes.Tail.compressionLengthBoundIter_le_exp2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:07:52.417041+00:00
-- url     : https://prove2.me/theorems/041952b8-1e7c-4997-add2-66c8b9fe2628
-- title:
--   Tail: compression Length Bound Iter le exp2
-- statement:
--   Compression is bounded by a single exponential coefficient times the initial length plus
--   one, uniformly in all natural-number parameters.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ElementaryBound.lean#L181-L214
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ElementaryBound.lean#L181-L214

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

theorem DeciSigma1.Holes.Tail.compressionLengthBoundIter_le_exp2 (k N D r E : ℕ) :
    compressionLengthBoundIter k N D r E ≤
      exp2 (16 * (k + N + D + r + 2) ^ 4) * (E + 1) := by sorry
