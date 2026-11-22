-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_streamPeriod_mul
-- name    : DeciSigma1.Arithmetic.streamPeriod_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:59:33.609667+00:00
-- url     : https://prove2.me/theorems/aecbeafe-6404-4144-87df-480ee7be2aeb
-- title:
--   Arithmetic: stream Period mul
-- statement:
--   The Arithmetic construction uses the stream Period mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/FinitePaths.lean#L294-L298
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/FinitePaths.lean#L294-L298

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Mathlib.Order.Nat
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
variable {β : Type*}
open DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Arithmetic.streamPeriod_mul {ξ : ℕ → α} {d : ℕ} (h : StreamPeriod ξ d) (a j : ℕ) :
    ξ (a + j * d) = ξ a := by sorry
