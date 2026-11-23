-- Prove2me | Theorems.Thm_Automata_greater_subseq_lemma
-- name    : Automata.greater_subseq_lemma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:31:28.395552+00:00
-- url     : https://prove2.me/theorems/dedc5e41-56fa-45d1-baf4-abdd6ea75b8e
-- title:
--   Automata: greater subseq lemma
-- statement:
--   A technical lemma for use in the next theorem.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/ChouekaLemma.lean#L42-L56
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/ChouekaLemma.lean#L42-L56

import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Mathlib_InfGraphRamsey
import Definitions.Def_AutomataTheory_Languages_ChouekaLemma
set_option autoImplicit true
open Function Set Filter Stream'
open scoped Computability
open Classical
attribute [local implicit_reducible] Stream'
open Automata
attribute [local instance_reducible] DA.toNA
variable {A : Type}

theorem Automata.greater_subseq_lemma (φ φ' : ℕ → ℕ) (hi : Injective φ') :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ n, φ (σ n) < φ' (σ (n + 1)) := by sorry
