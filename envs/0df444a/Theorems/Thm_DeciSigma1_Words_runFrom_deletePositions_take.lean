-- Prove2me | Theorems.Thm_DeciSigma1_Words_runFrom_deletePositions_take
-- name    : DeciSigma1.Words.runFrom_deletePositions_take
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:53:55.726008+00:00
-- url     : https://prove2.me/theorems/a8d83718-ebf3-4806-b405-52bff2a6ee4d
-- title:
--   Words: run From delete Positions take
-- statement:
--   Deleting maximal intervals whose two end cuts carry the same state preserves the state at
--   every cut that is not interior to a deleted interval.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L310-L343
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L310-L343

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

theorem DeciSigma1.Words.runFrom_deletePositions_take (T : Table α S k) (q : S) (w : List α)
    (hblock : ∀ j c, j < c → c ≤ w.length → (∀ p, j ≤ p → p < c → p ∈ D) →
      (j = 0 ∨ j - 1 ∉ D) → c ∉ D → runFrom T.step q (w.take j) = runFrom T.step q (w.take c))
    (c : ℕ) (hc : c ≤ w.length) (hint : c = 0 ∨ c ∉ D ∨ c - 1 ∉ D) :
    runFrom T.step q (deletePositions (w.take c) D) = runFrom T.step q (w.take c) := by sorry
