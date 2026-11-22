-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_compressionLengthBoundIter_le_log
-- name    : DeciSigma1.Holes.Tail.compressionLengthBoundIter_le_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:00:34.68231+00:00
-- url     : https://prove2.me/theorems/9f7c3ffb-4943-4f40-a881-32f0bd1e7701
-- title:
--   Tail: compression Length Bound Iter le log
-- statement:
--   Compression multiplies a common logarithmic bound by at most `16 * (r + 1)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedForm.lean#L35-L132
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedForm.lean#L35-L132

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ElementaryBound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_LevelElementaryBound
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedForm
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open Arithmetic

theorem DeciSigma1.Holes.Tail.compressionLengthBoundIter_le_log (k N D r E H : ℕ)
    (hH : 1 ≤ H) (hN : N ≤ exp2 H) (hfac : N.factorial ≤ exp2 H)
    (hhead : 2 ^ (k * (N - 1)) ≤ exp2 H) (hD : D ≤ exp2 H)
    (hr : r ≤ exp2 H) (hE : E ≤ exp2 H) :
    compressionLengthBoundIter k N D r E ≤ exp2 (16 * (r + 1) * H) := by sorry
