-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_Neg_word_nil
-- name    : DeciSigma1.Full.Closure.Neg.word_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:06:48.919794+00:00
-- url     : https://prove2.me/theorems/506aa33e-ae1b-437d-8644-e02cf0256650
-- title:
--   Neg: word nil
-- statement:
--   The Neg construction uses the word nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L265-L266
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L265-L266

module
public import Mathlib.Data.Fintype.Powerset
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Automata
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*}

theorem DeciSigma1.Full.Closure.Neg.word_nil {Γ : List (LitT n V)} {n : Config n V} (h : Neg Γ n) :
    n.2.2 = [] := by sorry
