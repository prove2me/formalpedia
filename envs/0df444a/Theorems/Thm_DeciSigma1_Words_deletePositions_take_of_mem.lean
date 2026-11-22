-- Prove2me | Theorems.Thm_DeciSigma1_Words_deletePositions_take_of_mem
-- name    : DeciSigma1.Words.deletePositions_take_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:15.193797+00:00
-- url     : https://prove2.me/theorems/d2af51cf-0b2e-427a-b8eb-dc36a3fd5b79
-- title:
--   Words: delete Positions take of mem
-- statement:
--   The Words construction uses the delete Positions take of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L218-L227
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L218-L227

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

theorem DeciSigma1.Words.deletePositions_take_of_mem (w : List α) {j c : ℕ} (hjc : j ≤ c)
    (h : ∀ p, j ≤ p → p < c → p ∈ D) : deletePositions (w.take c) D =
        deletePositions (w.take j) D := by sorry
