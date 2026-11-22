-- Prove2me | Theorems.Thm_DeciSigma1_Words_ChainBoundFrom_mono
-- name    : DeciSigma1.Words.ChainBoundFrom.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:42:45.848128+00:00
-- url     : https://prove2.me/theorems/e2cbb365-fea4-42c5-b62f-2f2bdffe2200
-- title:
--   Chain Bound From: mono
-- statement:
--   The Chain Bound From construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L242-L244
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L242-L244

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α : Type}
variable [DecidableEq α]

theorem DeciSigma1.Words.ChainBoundFrom.mono {t : List α} {b₀ b₁ Sb Sb' : ℕ} (h : ChainBoundFrom t b₀ Sb)
    (hb : b₀ ≤ b₁) (hS : Sb ≤ Sb') : ChainBoundFrom t b₁ Sb' := by sorry
