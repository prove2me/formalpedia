-- Prove2me | Theorems.Thm_DeciSigma1_Words_Ray_stream_add_stem
-- name    : DeciSigma1.Words.Ray.stream_add_stem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:53.377733+00:00
-- url     : https://prove2.me/theorems/e8d507ca-7960-4d05-a22c-66e8ad6e5b12
-- title:
--   Ray: stream add stem
-- statement:
--   The Ray construction uses the stream add stem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L355-L356
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L355-L356

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

theorem DeciSigma1.Words.Ray.stream_add_stem (t : ℕ) : Ω.stream (Ω.stem.length + t) = Ω.periodicTail t := by sorry
