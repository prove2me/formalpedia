-- Prove2me | Theorems.Thm_DeciSigma1_Words_chain_length_le_mortal
-- name    : DeciSigma1.Words.chain_length_le_mortal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:07:55.296578+00:00
-- url     : https://prove2.me/theorems/7cb8f904-8ef5-4560-a682-354ad124fc6a
-- title:
--   Words: chain length le mortal
-- statement:
--   A suffix chain of an eligible coordinate with a mortal endpoint has at most `|S| - 1`
--   members: its suffix starts carry distinct live states.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L302-L326
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L302-L326

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

theorem DeciSigma1.Words.chain_length_le_mortal (h : M.Eligible W j) (hm : ¬ M.Immortal (M.endState W j))
    {bs : List ℕ} (hbs : SuffixChain (W j) bs) : bs.length ≤ Fintype.card S - 1 := by sorry
