-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_mono
-- name    : DeciSigma1.Holes.Tail.suffixLengthEnvelope_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:10:28.92636+00:00
-- url     : https://prove2.me/theorems/1bf4a86b-a067-4b33-ac95-5347a2926846
-- title:
--   Tail: suffix Length Envelope mono
-- statement:
--   The Tail construction uses the suffix Length Envelope mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedFactors.lean#L110-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedFactors.lean#L110-L118

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Words
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Tail.suffixLengthEnvelope_mono (m N : ℕ) : ∀ Ss : List ℕ, Monotone (suffixLengthEnvelope m N Ss)
  := by sorry
