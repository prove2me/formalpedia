-- Prove2me | Theorems.Thm_DeciSigma1_runFrom_nil
-- name    : DeciSigma1.runFrom_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:33:06.102806+00:00
-- url     : https://prove2.me/theorems/7405897e-2c1f-4911-9021-c9c25734054d
-- title:
--   Deci Sigma1: run From nil
-- statement:
--   The Deci Sigma1 construction uses the run From nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Basic.lean#L42-L42
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Basic.lean#L42-L42

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

theorem DeciSigma1.runFrom_nil (δ : S → α → S) (q : S) : runFrom δ q [] = q := by sorry

attribute [defeq] DeciSigma1.runFrom_nil
