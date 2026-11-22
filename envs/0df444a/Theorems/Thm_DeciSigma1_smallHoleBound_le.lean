-- Prove2me | Theorems.Thm_DeciSigma1_smallHoleBound_le
-- name    : DeciSigma1.smallHoleBound_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:27:17.226264+00:00
-- url     : https://prove2.me/theorems/2b7a7d33-1abd-47d6-8e98-7c5f1e341649
-- title:
--   Deci Sigma1: small Hole Bound le
-- statement:
--   The small-hole bound is at most four iterated exponentials, independently of the alphabet
--   size. Its innermost argument is polynomial in `N` for each fixed `k`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Main.lean#L344-L396
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Main.lean#L344-L396

module
public import Definitions.Def_LeanPool_DeciSigma1_Encodings
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ElementaryBound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedForm
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Main
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1
open Arithmetic

theorem DeciSigma1.smallHoleBound_le (σ k N : ℕ) :
    smallHoleBound σ k N ≤ (fun x : ℕ => 2 ^ x)^[4]
      ((k + N + 20) ^ (2 * k + 6)) := by sorry
