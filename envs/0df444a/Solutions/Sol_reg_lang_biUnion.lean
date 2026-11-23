-- Prove2me | solution 1 for reg_lang_biUnion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:46:59.431567+00:00
-- url     : https://prove2.me/submissions/dd3d4a81-ac33-4867-a9bf-39da673cc0a3

import Definitions.Def_AutomataTheory_Automata_Sum
import Definitions.Def_AutomataTheory_Automata_Prod
import Definitions.Def_AutomataTheory_Automata_PSet
import Definitions.Def_AutomataTheory_Automata_Concat
import Definitions.Def_AutomataTheory_Automata_Loop
import Definitions.Def_AutomataTheory_Automata_Congr
import Definitions.Def_AutomataTheory_Languages_RegLang
import Theorems.Thm_reg_lang_empty
import Theorems.Thm_reg_lang_union

set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream'
open Classical
variable {A : Type}
theorem _root_.solution {I : Type} [Finite I] {s : Set I} {L : I → Set (List A)}
    (h : ∀ i ∈ s, RegLang (L i)) : RegLang (⋃ i ∈ s, L i) := by
  generalize h_n : s.ncard = n
  induction' n with n h_ind generalizing s
  . obtain ⟨rfl⟩ := (ncard_eq_zero (s := s)).mp h_n
    simp +instances [reg_lang_empty]
  obtain ⟨i, t, h_i, rfl, rfl⟩ := (ncard_eq_succ (s := s)).mp h_n
  simp ; apply reg_lang_union <;> grind
