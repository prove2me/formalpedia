-- Prove2me | Theorems.Thm_DeciSigma1_Words_retainedCount_add_of_not_mem
-- name    : DeciSigma1.Words.retainedCount_add_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:32.180807+00:00
-- url     : https://prove2.me/theorems/49b8bea4-0afc-4ed1-9a1e-9ccf22551d61
-- title:
--   Words: retained Count add of not mem
-- statement:
--   The Words construction uses the retained Count add of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L90-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L90-L97

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

theorem DeciSigma1.Words.retainedCount_add_of_not_mem {a n : ℕ} (h : ∀ i < n, a + i ∉ D) :
    retainedCount D (a + n) = retainedCount D a + n := by sorry
