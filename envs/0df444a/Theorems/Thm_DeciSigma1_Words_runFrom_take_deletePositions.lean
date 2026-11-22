-- Prove2me | Theorems.Thm_DeciSigma1_Words_runFrom_take_deletePositions
-- name    : DeciSigma1.Words.runFrom_take_deletePositions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:53:57.187977+00:00
-- url     : https://prove2.me/theorems/a75034eb-4cbe-46b6-a24e-3751e95527d4
-- title:
--   Words: run From take delete Positions
-- statement:
--   Under the hypothesis of `runFrom_deletePositions_take`, the state of the edited word at a
--   cut is the state of the original word at the greatest preimage of the cut.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L347-L367
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L347-L367

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

theorem DeciSigma1.Words.runFrom_take_deletePositions (T : Table α S k) (q : S) (w : List α)
    (hblock : ∀ j c, j < c → c ≤ w.length → (∀ p, j ≤ p → p < c → p ∈ D) →
      (j = 0 ∨ j - 1 ∉ D) → c ∉ D → runFrom T.step q (w.take j) = runFrom T.step q (w.take c))
    (hD : w.length ∉ D) (a : ℕ) :
    runFrom T.step q ((deletePositions w D).take a) =
        runFrom T.step q (w.take (greatestPreimage D a)) := by sorry
