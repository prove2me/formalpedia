-- Prove2me | Theorems.Thm_DeciSigma1_decideBooleanSentenceTopFree_correct
-- name    : DeciSigma1.decideBooleanSentenceTopFree_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:23:43.566177+00:00
-- url     : https://prove2.me/theorems/7c320100-d04f-40e9-be71-0a3cc956f648
-- title:
--   Deci Sigma1: decide Boolean Sentence Top Free correct
-- statement:
--   `decideBooleanSentenceTopFree` returns `true` exactly when the sentence holds in the
--   class.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Main.lean#L192-L195
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Main.lean#L192-L195

module
public import Definitions.Def_LeanPool_DeciSigma1_Encodings
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ElementaryBound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedForm
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Main
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1
variable {n : ℕ}

theorem DeciSigma1.decideBooleanSentenceTopFree_correct (C : Entailment.Logic.TreeClass)
    (φ : Entailment.Logic.BooleanSentence n) :
    @decide _ (decideBooleanSentenceTopFree C φ) = true ↔ φ.HoldsIn C.Contains := by sorry
