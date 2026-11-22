-- Prove2me | Theorems.Thm_DeciSigma1_decideBooleanSentence_correct
-- name    : DeciSigma1.decideBooleanSentence_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:23:41.248281+00:00
-- url     : https://prove2.me/theorems/84ce4c8a-44a5-46be-9673-af6d69922dcb
-- title:
--   Deci Sigma1: decide Boolean Sentence correct
-- statement:
--   `decideBooleanSentence` returns `true` exactly when the sentence holds in the class.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Main.lean#L173-L176
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Main.lean#L173-L176

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

theorem DeciSigma1.decideBooleanSentence_correct (c : Fin n → Bool) (C : Full.Logic.TreeClass)
    (φ : Full.Logic.BooleanSentence n) :
    @decide _ (decideBooleanSentence c C φ) = true ↔ φ.HoldsIn C.Contains c := by sorry
