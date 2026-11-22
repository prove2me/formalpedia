-- Prove2me | Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage_add
-- name    : DeciSigma1.Words.retainedCount_greatestPreimage_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:53:57.20788+00:00
-- url     : https://prove2.me/theorems/ecdce517-c1f4-498a-a176-da639f19b99f
-- title:
--   Words: retained Count greatest Preimage add
-- statement:
--   Along a stretch of retained positions that starts at the greatest preimage of `a`, the cut
--   map is a shift.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L416-L418
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L416-L418

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

theorem DeciSigma1.Words.retainedCount_greatestPreimage_add {a n : ℕ} (h : ∀ i < n, greatestPreimage D a + i ∉ D) :
    retainedCount D (greatestPreimage D a + n) = a + n := by sorry
