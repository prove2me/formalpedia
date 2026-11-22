-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
-- name    : DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:13.745573+00:00
-- url     : https://prove2.me/theorems/b5382a58-f64b-4dc3-ae5c-82b6ca3fcbe4
-- title:
--   Tail: suffix Length Envelope nil
-- statement:
--   The Tail construction uses the suffix Length Envelope nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedFactors.lean#L75-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedFactors.lean#L75-L75

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Words
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil (m N b : ℕ) : suffixLengthEnvelope m N [] b = b := by sorry

attribute [defeq] DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil
