-- Prove2me | Theorems.Thm_DeciSigma1_Words_Ray_streamPrefix_periodicTail
-- name    : DeciSigma1.Words.Ray.streamPrefix_periodicTail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:59:10.891266+00:00
-- url     : https://prove2.me/theorems/a1849ce5-2886-4ae2-8232-0fad97c9c9e6
-- title:
--   Ray: stream Prefix periodic Tail
-- statement:
--   The Ray construction uses the stream Prefix periodic Tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L555-L565
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L555-L565

module
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Words (pow)
variable {α : Type}
open DeciSigma1.Words.Ray
variable (Ω : Ray α)
variable {Ω}
variable [DecidableEq α]
omit [DecidableEq α]

theorem DeciSigma1.Words.Ray.streamPrefix_periodicTail (L : ℕ) :
    streamPrefix Ω.periodicTail L = (pow Ω.loop (L + 1)).take L := by sorry
