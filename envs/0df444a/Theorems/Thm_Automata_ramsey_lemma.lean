-- Prove2me | Theorems.Thm_Automata_ramsey_lemma
-- name    : Automata.ramsey_lemma
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:31:40.290151+00:00
-- url     : https://prove2.me/theorems/8cd66a09-5b9b-482f-b5d3-6e45d77d27c2
-- title:
--   Automata: ramsey lemma
-- statement:
--   This lemma derives a form of the Ramsey theorem suitable for use in the next theorem.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/ChouekaLemma.lean#L111-L149
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/ChouekaLemma.lean#L111-L149

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

theorem Automata.ramsey_lemma {C : Type} {cs : Set C} {φ : ℕ → ℕ} {col : ℕ → ℕ → C}
    (h_fin : cs.Finite) (h_mono : StrictMono φ) (h_col : ∀ i j, i < j → col (φ i) (φ j) ∈ cs) :
    ∃ c ∈ cs, ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ i j, i < j → col (φ (σ i)) (φ (σ j)) = c := by sorry
