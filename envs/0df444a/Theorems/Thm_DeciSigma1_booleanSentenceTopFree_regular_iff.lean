-- Prove2me | Theorems.Thm_DeciSigma1_booleanSentenceTopFree_regular_iff
-- name    : DeciSigma1.booleanSentenceTopFree_regular_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:26:22.288918+00:00
-- url     : https://prove2.me/theorems/eda51651-7085-40b4-b7df-fdba2722f5c0
-- title:
--   Deci Sigma1: boolean Sentence Top Free regular iff
-- statement:
--   Over `{⊥, f}`, a Boolean Σ₁/Π₁ sentence has the same truth value over regular and over
--   arbitrary trees.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Main.lean#L199-L201
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Main.lean#L199-L201

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

theorem DeciSigma1.booleanSentenceTopFree_regular_iff (φ : Entailment.Logic.BooleanSentence n) :
    φ.HoldsIn Semantics.IsRegularTree ↔ φ.HoldsIn (fun _ => True) := by sorry
