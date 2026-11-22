-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_mem_forbiddenPredecessors
-- name    : DeciSigma1.Full.Closure.mem_forbiddenPredecessors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:06:08.602725+00:00
-- url     : https://prove2.me/theorems/7c62824b-641f-4570-abb6-eccdcb1d95b4
-- title:
--   Closure: mem forbidden Predecessors
-- statement:
--   The Closure construction uses the mem forbidden Predecessors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L304-L306
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L304-L306

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

theorem DeciSigma1.Full.Closure.mem_forbiddenPredecessors {x : V × Bool} : x ∈ forbiddenPredecessors c Γ ↔
    ∃ n, Neg Γ n ∧ (x, (n.1, n.2.1)) ∈ Constraints.derivedPairs (signed c Γ) := by sorry
