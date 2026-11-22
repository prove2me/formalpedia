-- Prove2me | Theorems.Thm_DeciSigma1_runFrom_cons
-- name    : DeciSigma1.runFrom_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:33:07.699817+00:00
-- url     : https://prove2.me/theorems/dfa582b7-e0b1-459b-b10d-b864573d0fca
-- title:
--   Deci Sigma1: run From cons
-- statement:
--   The Deci Sigma1 construction uses the run From cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Basic.lean#L44-L45
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Basic.lean#L44-L45

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

theorem DeciSigma1.runFrom_cons (δ : S → α → S) (q : S) (c : α) (w : List α) :
    runFrom δ q (c :: w) = runFrom δ (δ q c) w := by sorry

attribute [defeq] DeciSigma1.runFrom_cons
