-- Prove2me | Theorems.Thm_DeciSigma1_booleanSentence_regular_iff
-- name    : DeciSigma1.booleanSentence_regular_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:23:25.663068+00:00
-- url     : https://prove2.me/theorems/3eae3eea-d0d6-4209-a4cf-4fffef78f79a
-- title:
--   Deci Sigma1: boolean Sentence regular iff
-- statement:
--   Over `{⊥, f, ⊤}`, a Boolean Σ₁/Π₁ sentence has the same truth value over regular and over
--   arbitrary trees.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Main.lean#L180-L182
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Main.lean#L180-L182

module
public import Definitions.Def_LeanPool_DeciSigma1_Encodings
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ElementaryBound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedForm
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Main
public import Theorems.Thm_DeciSigma1_Entailment_Logic_booleanSentence_regular_iff
public import Theorems.Thm_DeciSigma1_Full_Logic_booleanSentence_regular_iff

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1
variable {n : ℕ}

theorem DeciSigma1.booleanSentence_regular_iff (c : Fin n → Bool) (φ : Full.Logic.BooleanSentence n) :
    φ.HoldsIn Full.Models.RegularTop c ↔ φ.HoldsIn (fun _ => True) c := by sorry
