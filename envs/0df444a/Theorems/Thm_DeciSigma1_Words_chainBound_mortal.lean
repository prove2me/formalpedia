-- Prove2me | Theorems.Thm_DeciSigma1_Words_chainBound_mortal
-- name    : DeciSigma1.Words.chainBound_mortal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:07:59.244809+00:00
-- url     : https://prove2.me/theorems/d905b16b-23d2-4971-ae50-a57457e4b38d
-- title:
--   Words: chain Bound mortal
-- statement:
--   On an eligible coordinate with a mortal endpoint, chains have at most `|S| - 1` members.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L329-L331
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L329-L331

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
variable {S : Type} [Fintype S] {k : ℕ} (M : StructuralReader α S k)
  {W : Fin k → List α} {j : Fin k}
variable {M}

theorem DeciSigma1.Words.chainBound_mortal (h : M.Eligible W j) (hm : ¬ M.Immortal (M.endState W j)) :
    ChainBound (W j) (Fintype.card S - 1) := by sorry
