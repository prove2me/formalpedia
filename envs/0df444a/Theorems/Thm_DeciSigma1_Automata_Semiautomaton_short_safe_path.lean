-- Prove2me | Theorems.Thm_DeciSigma1_Automata_Semiautomaton_short_safe_path
-- name    : DeciSigma1.Automata.Semiautomaton.short_safe_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:40.060731+00:00
-- url     : https://prove2.me/theorems/1fb70e89-2948-4a01-9024-44d2b99dec75
-- title:
--   Semiautomaton: short safe path
-- statement:
--   A run inside a set of states can be shortened, by deleting loops, to one of length less than the
--   number of states with the same endpoint.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Basic.lean#L110-L138
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Basic.lean#L110-L138

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

theorem DeciSigma1.Automata.Semiautomaton.short_safe_path [Fintype S] (M : Semiautomaton α S) (G : S → Prop) (q : S)
    (w : Word α) (h : M.PathSafe G q w) :
    ∃ v, v.length < Fintype.card S ∧ M.PathSafe G q v ∧
      runFrom M.step q v = runFrom M.step q w := by sorry
