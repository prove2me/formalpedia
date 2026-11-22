-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_cons
-- name    : DeciSigma1.Holes.Tail.suffixLengthBound_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:49:15.954803+00:00
-- url     : https://prove2.me/theorems/0cb3a193-b9c3-4f22-aca5-c44118660169
-- title:
--   Tail: suffix Length Bound cons
-- statement:
--   The Tail construction uses the suffix Length Bound cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedFactors.lean#L77-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedFactors.lean#L77-L81

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Words
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Tail.suffixLengthBound_cons (m N S : ℕ) (Ss : List ℕ) (b : ℕ) :
    suffixLengthBound m N (S :: Ss) b =
      2 * suffixLengthBound m N Ss ((fun b => b + suffixLengthBound m N Ss b)^[S] b) +
        suffixLengthBound m N Ss ((fun b => b + suffixLengthBound m N Ss b)^[S] b +
          suffixLengthBound m N Ss ((fun b => b + suffixLengthBound m N Ss b)^[S] b)) + 2 := by sorry
