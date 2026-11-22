-- Prove2me | Theorems.Thm_DeciSigma1_Words_retainedCount_union_Ico_of_le
-- name    : DeciSigma1.Words.retainedCount_union_Ico_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:28.08208+00:00
-- url     : https://prove2.me/theorems/6eeaeabf-91d3-4c70-b893-8899b9ff99cd
-- title:
--   Words: retained Count union Ico of le
-- statement:
--   The Words construction uses the retained Count union Ico of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L446-L450
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L446-L450

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

theorem DeciSigma1.Words.retainedCount_union_Ico_of_le {p : ℕ} (hp : p ≤ c) :
    retainedCount (D ∪ Finset.Ico c (c + δ)) p = retainedCount D p := by sorry
