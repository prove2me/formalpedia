-- Prove2me | Theorems.Thm_DeciSigma1_Words_streamPeriod_gcd
-- name    : DeciSigma1.Words.streamPeriod_gcd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:38.91993+00:00
-- url     : https://prove2.me/theorems/3aaf0ee6-e8e6-4c5d-bcdb-43c5b081a32c
-- title:
--   Words: stream Period gcd
-- statement:
--   The Words construction uses the stream Period gcd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L124-L133
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L124-L133

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
variable {α : Type*}

theorem DeciSigma1.Words.streamPeriod_gcd {ξ : ℕ → α} {p q : ℕ}
    (hp : StreamPeriod ξ p) (hq : StreamPeriod ξ q) : StreamPeriod ξ (Nat.gcd p q) := by sorry
