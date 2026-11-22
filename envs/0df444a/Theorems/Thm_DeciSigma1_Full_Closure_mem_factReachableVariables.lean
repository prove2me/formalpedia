-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_mem_factReachableVariables
-- name    : DeciSigma1.Full.Closure.mem_factReachableVariables
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:09:23.339137+00:00
-- url     : https://prove2.me/theorems/f1e78d60-3d41-4677-bb9b-a86aa7f498ba
-- title:
--   Closure: mem fact Reachable Variables
-- statement:
--   The Closure construction uses the mem fact Reachable Variables property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L294-L302
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L294-L302

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
variable [Fintype V] [DecidableEq V]
variable (c : Fin n → Bool) (Γ : List (LitT n V))
variable {c Γ}

theorem DeciSigma1.Full.Closure.mem_factReachableVariables {x : V × Bool} : x ∈ factReachableVariables c Γ ↔
    ∃ f β, Fact Γ f ∧ x ∈ Automata.upperRun (signed c Γ) (f.1, f.2.1) β := by sorry
