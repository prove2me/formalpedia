-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_upperRun_nil_absorb
-- name    : DeciSigma1.Full.Closure.upperRun_nil_absorb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:08:58.112796+00:00
-- url     : https://prove2.me/theorems/8bc43772-b14c-47a1-9035-cda1c630995b
-- title:
--   Closure: upper Run nil absorb
-- statement:
--   The Closure construction uses the upper Run nil absorb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L188-L194
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L188-L194

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

theorem DeciSigma1.Full.Closure.upperRun_nil_absorb {x : V × Bool} {β : List (Fin n)}
    (h : Automata.upperRun (signed c Γ) x β = ∅) (γ : List (Fin n)) :
    Automata.upperRun (signed c Γ) x (β ++ γ) = ∅ := by sorry
