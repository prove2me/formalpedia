-- Prove2me | Theorems.Thm_DeciSigma1_runFrom_snoc
-- name    : DeciSigma1.runFrom_snoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:33:12.710694+00:00
-- url     : https://prove2.me/theorems/b9a1f74c-9f2a-4dab-b457-9da825604c57
-- title:
--   Deci Sigma1: run From snoc
-- statement:
--   The Deci Sigma1 construction uses the run From snoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Basic.lean#L50-L52
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Basic.lean#L50-L52

module
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Card
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1
variable {α S : Type*}

theorem DeciSigma1.runFrom_snoc (δ : S → α → S) (q : S) (u : List α) (c : α) :
    runFrom δ q (u ++ [c]) = δ (runFrom δ q u) c := by sorry
