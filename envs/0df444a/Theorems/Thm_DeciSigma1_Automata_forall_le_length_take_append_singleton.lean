-- Prove2me | Theorems.Thm_DeciSigma1_Automata_forall_le_length_take_append_singleton
-- name    : DeciSigma1.Automata.forall_le_length_take_append_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:27:58.164359+00:00
-- url     : https://prove2.me/theorems/eebbd78e-a901-4339-a7ac-f3cc375dde96
-- title:
--   Automata: forall le length take append singleton
-- statement:
--   The Automata construction uses the forall le length take append singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L68-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L68-L81

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
variable {α S T : Type}

theorem DeciSigma1.Automata.forall_le_length_take_append_singleton {β : Type} (p : List β → Prop) (w : List β)
    (a : β) : (∀ j ≤ (w ++ [a]).length, p ((w ++ [a]).take j)) ↔
      (∀ j ≤ w.length, p (w.take j)) ∧ p (w ++ [a]) := by sorry
