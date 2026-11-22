-- Prove2me | Theorems.Thm_DeciSigma1_Entailment_Logic_booleanSentence_regular_iff
-- name    : DeciSigma1.Entailment.Logic.booleanSentence_regular_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:19:09.082126+00:00
-- url     : https://prove2.me/theorems/68ed3ead-d68b-46a5-acdb-fcf6e9702931
-- title:
--   Logic: boolean Sentence regular iff
-- statement:
--   A sentence over `{⊥, f}` has the same truth value over regular and over arbitrary
--   trees.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Logic.lean#L229-L234
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Logic.lean#L229-L234

module
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Logic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Entailment DeciSigma1.Entailment.Logic
open DeciSigma1.Constraints.TopFree DeciSigma1.Semantics
variable {n : ℕ} {V W : Type}
variable [Fintype V] [DecidableEq V]

theorem DeciSigma1.Entailment.Logic.booleanSentence_regular_iff (φ : BooleanSentence n) :
    φ.HoldsIn IsRegularTree ↔ φ.HoldsIn (fun _ => True) := by sorry
