-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_popRoot
-- name    : DeciSigma1.Full.Closure.popRoot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:08:44.85022+00:00
-- url     : https://prove2.me/theorems/d3e36f0e-9571-4009-8048-02aeb81da90e
-- title:
--   Closure: pop Root
-- statement:
--   The Closure construction uses the pop Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L180-L186
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L180-L186

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
open DeciSigma1.Semantics DeciSigma1.Constraints
variable {n : ℕ} {V : Type*}
variable {c : Fin n → Bool} {Γ : List (LitT n V)}
variable [Fintype V] [DecidableEq V]

theorem DeciSigma1.Full.Closure.popRoot {x : V × Bool} {β : List (Fin n)} {i : Fin n}
    (h : (Automata.upperRun (signed c Γ) x (β ++ [i])).Nonempty) :
    ∃ r ∈ Automata.upperRun (signed c Γ) x β, Neg Γ (r.1, r.2, []) := by sorry
