-- Prove2me | Theorems.Thm_DeciSigma1_Words_Ray_streamPrefix_stream
-- name    : DeciSigma1.Words.Ray.streamPrefix_stream
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:59:12.012403+00:00
-- url     : https://prove2.me/theorems/44633cb9-93fc-4de3-b39d-504fa4f4e4f0
-- title:
--   Ray: stream Prefix stream
-- statement:
--   The prefix of length `|stem| + L` of a ray is `stem ++ (loop^(L+1)).take L`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L569-L571
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L569-L571

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

theorem DeciSigma1.Words.Ray.streamPrefix_stream (L : ℕ) :
    streamPrefix Ω.stream (Ω.stem.length + L) = Ω.stem ++ (pow Ω.loop (L + 1)).take L := by sorry
