-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_compressionIntercept_mono
-- name    : DeciSigma1.Holes.Tail.compressionIntercept_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:00:17.946564+00:00
-- url     : https://prove2.me/theorems/20e6bf43-5350-4446-9bf1-21796ea0c748
-- title:
--   Tail: compression Intercept mono
-- statement:
--   The intercept increases with the number of remaining runs.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ElementaryBound.lean#L61-L64
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ElementaryBound.lean#L61-L64

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

theorem DeciSigma1.Holes.Tail.compressionIntercept_mono (k N D : ℕ) : Monotone (compressionIntercept k N D) := by sorry
