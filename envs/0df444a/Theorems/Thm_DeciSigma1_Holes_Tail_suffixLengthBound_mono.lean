-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_mono
-- name    : DeciSigma1.Holes.Tail.suffixLengthBound_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:52:19.365942+00:00
-- url     : https://prove2.me/theorems/ad754f2a-e11d-4149-a788-adc5d0dd3411
-- title:
--   Tail: suffix Length Bound mono
-- statement:
--   The Tail construction uses the suffix Length Bound mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedFactors.lean#L97-L108
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedFactors.lean#L97-L108

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Words
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Tail.suffixLengthBound_mono (m N : ℕ) : ∀ Ss : List ℕ, Monotone (suffixLengthBound m N Ss)
  := by sorry
