-- Prove2me | Theorems.Thm_DeciSigma1_Words_Ray_suffixBeforeOnset_suffix_prefixBeforeOnset
-- name    : DeciSigma1.Words.Ray.suffixBeforeOnset_suffix_prefixBeforeOnset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:57.208803+00:00
-- url     : https://prove2.me/theorems/26684993-8f72-4504-8ddd-81deeedd31d4
-- title:
--   Ray: suffix Before Onset suffix prefix Before Onset
-- statement:
--   The Ray construction uses the suffix Before Onset suffix prefix Before Onset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L547-L550
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L547-L550

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

theorem DeciSigma1.Words.Ray.suffixBeforeOnset_suffix_prefixBeforeOnset (Ω : Ray α) (J : ℕ) :
    Ω.suffixBeforeOnset J <:+ Ω.prefixBeforeOnset := by sorry
