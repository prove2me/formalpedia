-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_mem_negList
-- name    : DeciSigma1.Full.Closure.mem_negList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:05:34.481662+00:00
-- url     : https://prove2.me/theorems/0c36aef8-3022-4cde-b3a0-cf9228471837
-- title:
--   Closure: mem neg List
-- statement:
--   The Closure construction uses the mem neg List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L250-L260
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L250-L260

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

theorem DeciSigma1.Full.Closure.mem_negList {Γ : List (LitT n V)} {n : Config n V} :
    n ∈ negList Γ ↔ Neg Γ n := by sorry
