-- Prove2me | Theorems.Thm_DeciSigma1_Automata_Semiautomaton_pathSafe_append
-- name    : DeciSigma1.Automata.Semiautomaton.pathSafe_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:38.958104+00:00
-- url     : https://prove2.me/theorems/305b59a2-8e04-45b0-89fc-a114a6477296
-- title:
--   Semiautomaton: path Safe append
-- statement:
--   The Semiautomaton construction uses the path Safe append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Basic.lean#L96-L106
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Basic.lean#L96-L106

module
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Card
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Automata
variable {α : Type*}
open DeciSigma1.Automata.Semiautomaton
variable {S : Type*}

theorem DeciSigma1.Automata.Semiautomaton.pathSafe_append (M : Semiautomaton α S) (G : S → Prop) (q : S) (u v : Word α) :
    M.PathSafe G q (u ++ v) ↔
      M.PathSafe G q u ∧ M.PathSafe G (runFrom M.step q u) v := by sorry
