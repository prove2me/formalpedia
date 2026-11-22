-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_pad
-- name    : DeciSigma1.Holes.Tail.suffixLengthBound_pad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:10:37.490392+00:00
-- url     : https://prove2.me/theorems/006e2ddc-bb33-42e3-b0b9-4a2911e5afd8
-- title:
--   Tail: suffix Length Bound pad
-- statement:
--   At most `m` targets, each with chain budget `S` from `b₀`, can be handled with the budget
--   list `replicate m S`, by adding empty targets.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedFactors.lean#L275-L294
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedFactors.lean#L275-L294

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Words
variable {α S : Type} {k : ℕ}
variable [DecidableEq α] [Fintype S]
variable (T : Readers.Table α S k) (q0 : S) (x : List α)

theorem DeciSigma1.Holes.Tail.suffixLengthBound_pad (ts : List (List α)) {m S b₀ : ℕ} (hm : ts.length ≤ m)
    (hS : ∀ t ∈ ts, ChainBoundFrom t b₀ S) :
    ∃ ts' : List (List α), (∀ t ∈ ts, t ∈ ts') ∧
        List.Forall₂ (fun t S => ChainBoundFrom t b₀ S) ts' (List.replicate m S) := by sorry
