-- Prove2me | Theorems.Thm_DeciSigma1_Words_retainedCount_union_Ico_of_ge
-- name    : DeciSigma1.Words.retainedCount_union_Ico_of_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:35.757598+00:00
-- url     : https://prove2.me/theorems/1bb883e2-9f92-4414-a720-a98248571ab8
-- title:
--   Words: retained Count union Ico of ge
-- statement:
--   The Words construction uses the retained Count union Ico of ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L452-L464
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L452-L464

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}
variable {c δ : ℕ}

theorem DeciSigma1.Words.retainedCount_union_Ico_of_ge (hD : ∀ p ∈ D, p < c) {p : ℕ} (hp : c + δ ≤ p) :
    retainedCount (D ∪ Finset.Ico c (c + δ)) p = retainedCount D (p - δ) := by sorry
