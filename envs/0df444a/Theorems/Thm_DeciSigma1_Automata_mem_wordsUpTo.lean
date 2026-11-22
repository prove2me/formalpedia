-- Prove2me | Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
-- name    : DeciSigma1.Automata.mem_wordsUpTo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:33:09.297796+00:00
-- url     : https://prove2.me/theorems/27f646f3-4178-45ef-9324-4dc777aa52e6
-- title:
--   Automata: mem words Up To
-- statement:
--   The Automata construction uses the mem words Up To property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Basic.lean#L148-L155
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Basic.lean#L148-L155

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

theorem DeciSigma1.Automata.mem_wordsUpTo [Fintype α] [DecidableEq α] (w : Word α) (n : ℕ) :
    w ∈ wordsUpTo n ↔ w.length ≤ n := by sorry
