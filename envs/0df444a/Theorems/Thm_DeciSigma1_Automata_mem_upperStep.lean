-- Prove2me | Theorems.Thm_DeciSigma1_Automata_mem_upperStep
-- name    : DeciSigma1.Automata.mem_upperStep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:19:35.784795+00:00
-- url     : https://prove2.me/theorems/4962b8e7-d90d-48af-ae05-8530179fe086
-- title:
--   Automata: mem upper Step
-- statement:
--   The Automata construction uses the mem upper Step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L190-L198
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L190-L198

module
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1
open DeciSigma1.Constraints
open DeciSigma1.Automata
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

theorem DeciSigma1.Automata.mem_upperStep {Γ : List (LitT n V)} {S : Finset V} {c : Fin n} {b : V} :
    b ∈ upperStep Γ S c ↔ ∃ r ∈ S, ∃ bs, LitT.leF r bs ∈ Γ ∧
      ((bs c), b) ∈ derivedPairs Γ := by sorry
