-- Prove2me | Theorems.Thm_DeciSigma1_Words_eq_of_retainedCount_eq
-- name    : DeciSigma1.Words.eq_of_retainedCount_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:02.337806+00:00
-- url     : https://prove2.me/theorems/047a0844-ed48-496f-a0d1-0b39f81070e9
-- title:
--   Words: eq of retained Count eq
-- statement:
--   Two cuts with the same image, neither of which ends a deleted interval, are equal.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L140-L149
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L140-L149

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

theorem DeciSigma1.Words.eq_of_retainedCount_eq {p q : ℕ} (h : retainedCount D p = retainedCount D q)
    (hp : p = 0 ∨ p - 1 ∉ D) (hq : q = 0 ∨ q - 1 ∉ D) : p = q := by sorry
