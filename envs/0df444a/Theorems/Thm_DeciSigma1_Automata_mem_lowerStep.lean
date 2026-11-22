-- Prove2me | Theorems.Thm_DeciSigma1_Automata_mem_lowerStep
-- name    : DeciSigma1.Automata.mem_lowerStep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:19:41.973799+00:00
-- url     : https://prove2.me/theorems/4d02d25f-b097-4e1d-bf80-1555faf72d78
-- title:
--   Automata: mem lower Step
-- statement:
--   The Automata construction uses the mem lower Step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L199-L207
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L199-L207

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

theorem DeciSigma1.Automata.mem_lowerStep {Γ : List (LitT n V)} {S : Finset V} {c : Fin n} {a : V} :
    a ∈ lowerStep Γ S c ↔ ∃ r ∈ S, ∃ as, LitT.fLe as r ∈ Γ ∧
      (a, (as c)) ∈ derivedPairs Γ := by sorry
