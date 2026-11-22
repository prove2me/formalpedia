-- Prove2me | Theorems.Thm_DeciSigma1_Automata_upperRun_closed
-- name    : DeciSigma1.Automata.upperRun_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:22:35.35319+00:00
-- url     : https://prove2.me/theorems/81e8043b-4484-43ee-b11d-61795264f6fe
-- title:
--   Automata: upper Run closed
-- statement:
--   The Automata construction uses the upper Run closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L219-L226
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L219-L226

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

theorem DeciSigma1.Automata.upperRun_closed {Γ : List (LitT n V)} {x a b : V} {w : List (Fin n)}
    (ha : a ∈ upperRun Γ x w) (hab : (a, b) ∈ derivedPairs Γ) : b ∈ upperRun Γ x w := by sorry
