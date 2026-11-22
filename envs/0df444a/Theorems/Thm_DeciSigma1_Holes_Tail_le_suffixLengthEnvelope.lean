-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_le_suffixLengthEnvelope
-- name    : DeciSigma1.Holes.Tail.le_suffixLengthEnvelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:10:31.903047+00:00
-- url     : https://prove2.me/theorems/e7f0801d-bfbc-4224-925e-1d7bccfcab95
-- title:
--   Tail: le suffix Length Envelope
-- statement:
--   The Tail construction uses the le suffix Length Envelope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedFactors.lean#L120-L129
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedFactors.lean#L120-L129

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Words
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Tail.le_suffixLengthEnvelope (m N : ℕ) :
    ∀ (Ss : List ℕ) (b : ℕ), b ≤ suffixLengthEnvelope m N Ss b
  := by sorry
