-- Prove2me | Theorems.Thm_DeciSigma1_Words_le_greatestPreimage_iff
-- name    : DeciSigma1.Words.le_greatestPreimage_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:31.881529+00:00
-- url     : https://prove2.me/theorems/c8c67c1e-96fe-422f-8ee0-4284157a07ce
-- title:
--   Words: le greatest Preimage iff
-- statement:
--   `greatestPreimage D` is the upper adjoint of the cut map.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L236-L244
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L236-L244

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

theorem DeciSigma1.Words.le_greatestPreimage_iff {p a : ℕ} : p ≤ greatestPreimage D a ↔ retainedCount D p ≤ a := by sorry
