-- Prove2me | Theorems.Thm_DeciSigma1_Automata_mem_up
-- name    : DeciSigma1.Automata.mem_up
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:19:59.009443+00:00
-- url     : https://prove2.me/theorems/da480dce-0918-43b4-a545-4fe473cb6207
-- title:
--   Automata: mem up
-- statement:
--   The Automata construction uses the mem up property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L186-L187
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L186-L187

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

theorem DeciSigma1.Automata.mem_up {Γ : List (LitT n V)} {x y : V} :
    y ∈ up Γ x ↔ (x, y) ∈ derivedPairs Γ := by sorry
