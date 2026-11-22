-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_splitPieceLengthBound_eq_affine
-- name    : DeciSigma1.Holes.Tail.splitPieceLengthBound_eq_affine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:00:43.420016+00:00
-- url     : https://prove2.me/theorems/6d9b514d-1d28-483a-b2d5-3bac7e53f5bb
-- title:
--   Tail: split Piece Length Bound eq affine
-- statement:
--   The split piece cap is exactly affine in the uncovered length.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ElementaryBound.lean#L49-L58
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ElementaryBound.lean#L49-L58

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

theorem DeciSigma1.Holes.Tail.splitPieceLengthBound_eq_affine (k N D r E : ℕ) :
    Periodic.pieceLengthBound N D (k * (N - 1)) (2 * r + E) =
      compressionIntercept k N D r + compressionSlope k N D * E := by sorry
