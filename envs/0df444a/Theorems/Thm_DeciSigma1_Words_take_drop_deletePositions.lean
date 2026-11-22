-- Prove2me | Theorems.Thm_DeciSigma1_Words_take_drop_deletePositions
-- name    : DeciSigma1.Words.take_drop_deletePositions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:22.076037+00:00
-- url     : https://prove2.me/theorems/0973a5a0-3f55-425e-a225-a78ef70b1a61
-- title:
--   Words: take drop delete Positions
-- statement:
--   If no junction lies strictly between the cuts `a` and `a + n` of the edited word, the `n`
--   letters of the edited word read from `a` are the `n` letters of the original word read from the
--   greatest preimage of `a`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L423-L434
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L423-L434

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

theorem DeciSigma1.Words.take_drop_deletePositions (w : List α) {a n : ℕ}
    (hJ : ∀ p ∈ D, ¬ (a < retainedCount D p ∧ retainedCount D p < a + n)) :
    ((deletePositions w D).drop a).take n = (w.drop (greatestPreimage D a)).take n := by sorry
