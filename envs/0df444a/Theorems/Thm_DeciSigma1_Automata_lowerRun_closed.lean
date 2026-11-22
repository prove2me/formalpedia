-- Prove2me | Theorems.Thm_DeciSigma1_Automata_lowerRun_closed
-- name    : DeciSigma1.Automata.lowerRun_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:28:08.257821+00:00
-- url     : https://prove2.me/theorems/a06a4c55-c886-4db3-a1b5-9c40f2bf07b2
-- title:
--   Automata: lower Run closed
-- statement:
--   The Automata construction uses the lower Run closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L228-L235
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L228-L235

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

theorem DeciSigma1.Automata.lowerRun_closed {Γ : List (LitT n V)} {y a b : V} {w : List (Fin n)}
    (ha : a ∈ lowerRun Γ y w) (hba : (b, a) ∈ derivedPairs Γ) : b ∈ lowerRun Γ y w := by sorry
