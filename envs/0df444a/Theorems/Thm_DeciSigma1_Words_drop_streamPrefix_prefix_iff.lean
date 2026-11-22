-- Prove2me | Theorems.Thm_DeciSigma1_Words_drop_streamPrefix_prefix_iff
-- name    : DeciSigma1.Words.drop_streamPrefix_prefix_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:40.493886+00:00
-- url     : https://prove2.me/theorems/41871a15-4fe2-4994-af58-a568998dd792
-- title:
--   Words: drop stream Prefix prefix iff
-- statement:
--   A suffix of a prefix of `η` is a prefix of a suffix of a prefix of `ξ` if and only if it is
--   not longer and the two infinite words agree on its length. This is the form in which channels
--   compare prefixes of rays.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L294-L297
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L294-L297

module
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Words (pow)
variable {α : Type}

theorem DeciSigma1.Words.drop_streamPrefix_prefix_iff (ξ η : ℕ → α) {L L' a b : ℕ} (hb : b ≤ L) (ha : a ≤ L') :
    (streamPrefix η L).drop b <+: (streamPrefix ξ L').drop a ↔
      L - b ≤ L' - a ∧ ∀ t < L - b, η (b + t) = ξ (a + t) := by sorry
