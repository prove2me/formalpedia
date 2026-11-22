-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_tailLengthBound_le_double_exp2
-- name    : DeciSigma1.Holes.Tail.tailLengthBound_le_double_exp2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:00:28.693303+00:00
-- url     : https://prove2.me/theorems/cbfefd0f-f0de-4fd2-8737-5ffbe8194dfd
-- title:
--   Tail: tail Length Bound le double exp2
-- statement:
--   The rejected-tail bound is at most a double exponential, uniformly in the alphabet size.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedForm.lean#L276-L278
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedForm.lean#L276-L278

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

theorem DeciSigma1.Holes.Tail.tailLengthBound_le_double_exp2 (σ k N : ℕ) :
    tailLengthBound σ k N ≤ exp2 (exp2 ((k + N + 20) ^ (2 * k + 5))) := by sorry
