-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
-- name    : DeciSigma1.Holes.Tail.suffixLengthBound_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:10.053804+00:00
-- url     : https://prove2.me/theorems/5991cc5b-4331-49c1-b55b-d82184be96d4
-- title:
--   Tail: suffix Length Bound nil
-- statement:
--   The Tail construction uses the suffix Length Bound nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedFactors.lean#L72-L73
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedFactors.lean#L72-L73

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Words
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Tail.suffixLengthBound_nil (m N b : ℕ) :
    suffixLengthBound m N [] b = factorLengthBound m N b + 1 := by sorry

attribute [defeq] DeciSigma1.Holes.Tail.suffixLengthBound_nil
