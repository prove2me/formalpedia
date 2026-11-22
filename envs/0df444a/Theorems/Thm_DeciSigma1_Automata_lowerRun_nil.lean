-- Prove2me | Theorems.Thm_DeciSigma1_Automata_lowerRun_nil
-- name    : DeciSigma1.Automata.lowerRun_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:19:50.217797+00:00
-- url     : https://prove2.me/theorems/f288d565-cf05-4943-bb5f-4357e5ac88d0
-- title:
--   Automata: lower Run nil
-- statement:
--   The Automata construction uses the lower Run nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L208-L208
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L208-L208

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

theorem DeciSigma1.Automata.lowerRun_nil (Γ : List (LitT n V)) (x : V) : lowerRun Γ x [] = down Γ x := by sorry

attribute [defeq] DeciSigma1.Automata.lowerRun_nil
