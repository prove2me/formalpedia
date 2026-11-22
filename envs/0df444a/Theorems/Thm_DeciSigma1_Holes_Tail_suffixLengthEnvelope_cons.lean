-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_cons
-- name    : DeciSigma1.Holes.Tail.suffixLengthEnvelope_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:49:24.355817+00:00
-- url     : https://prove2.me/theorems/9880a351-6e41-4315-957d-0c46ed5beda4
-- title:
--   Tail: suffix Length Envelope cons
-- statement:
--   The Tail construction uses the suffix Length Envelope cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedFactors.lean#L83-L86
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedFactors.lean#L83-L86

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Words
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Tail.suffixLengthEnvelope_cons (m N S : ℕ) (Ss : List ℕ) (b : ℕ) :
    suffixLengthEnvelope m N (S :: Ss) b =
      suffixLengthEnvelope m N Ss ((fun b => b + suffixLengthBound m N Ss b)^[S] b +
        suffixLengthBound m N Ss ((fun b => b + suffixLengthBound m N Ss b)^[S] b)) := by sorry
