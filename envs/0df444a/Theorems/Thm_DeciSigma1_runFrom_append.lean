-- Prove2me | Theorems.Thm_DeciSigma1_runFrom_append
-- name    : DeciSigma1.runFrom_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:34:17.444681+00:00
-- url     : https://prove2.me/theorems/8283b923-4598-4e52-95bc-db4c2796ca0c
-- title:
--   Deci Sigma1: run From append
-- statement:
--   The Deci Sigma1 construction uses the run From append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Basic.lean#L47-L48
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Basic.lean#L47-L48

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

theorem DeciSigma1.runFrom_append (δ : S → α → S) (q : S) (u v : List α) :
    runFrom δ q (u ++ v) = runFrom δ (runFrom δ q u) v := by sorry
