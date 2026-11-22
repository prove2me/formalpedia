-- Prove2me | Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
-- name    : DeciSigma1.Words.Ray.length_suffixBeforeOnset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:38.582325+00:00
-- url     : https://prove2.me/theorems/5a3037cd-413c-4707-9f84-6290f502ba5e
-- title:
--   Ray: length suffix Before Onset
-- statement:
--   The Ray construction uses the length suffix Before Onset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L544-L545
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L544-L545

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

theorem DeciSigma1.Words.Ray.length_suffixBeforeOnset (Ω : Ray α) (J : ℕ) :
    (Ω.suffixBeforeOnset J).length = Ω.onset - J := by sorry
