-- Prove2me | Theorems.Thm_DeciSigma1_Automata_Semiautomaton_pathSafe_iff
-- name    : DeciSigma1.Automata.Semiautomaton.pathSafe_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:37:35.7158+00:00
-- url     : https://prove2.me/theorems/432bdac3-b963-4104-b67f-e6ace673c370
-- title:
--   Semiautomaton: path Safe iff
-- statement:
--   The Semiautomaton construction uses the path Safe iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Basic.lean#L82-L94
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Basic.lean#L82-L94

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

theorem DeciSigma1.Automata.Semiautomaton.pathSafe_iff (M : Semiautomaton α S) (G : S → Prop) (q : S) (w : Word α) :
    M.PathSafe G q w ↔ ∀ j ≤ w.length, G (runFrom M.step q (w.take j)) := by sorry
