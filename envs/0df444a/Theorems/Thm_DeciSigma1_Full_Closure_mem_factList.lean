-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_mem_factList
-- name    : DeciSigma1.Full.Closure.mem_factList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:05:36.468086+00:00
-- url     : https://prove2.me/theorems/1a648173-1244-49b2-8c5e-a914b557c824
-- title:
--   Closure: mem fact List
-- statement:
--   The Closure construction uses the mem fact List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L238-L248
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L238-L248

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

theorem DeciSigma1.Full.Closure.mem_factList {Γ : List (LitT n V)} {f : Config n V} :
    f ∈ factList Γ ↔ Fact Γ f := by sorry
