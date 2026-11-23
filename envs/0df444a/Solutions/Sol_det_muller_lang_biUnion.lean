-- Prove2me | solution 1 for det_muller_lang_biUnion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:52:57.156567+00:00
-- url     : https://prove2.me/submissions/f7c12a84-4aaa-4be6-9112-310e0b368971

import Definitions.Def_AutomataTheory_Automata_DetConcat
import Definitions.Def_AutomataTheory_Automata_DetProd
import Definitions.Def_AutomataTheory_Languages_OmegaRegLang
import Definitions.Def_AutomataTheory_Languages_DetMullerLang
import Theorems.Thm_det_muller_lang_empty
import Theorems.Thm_det_muller_lang_union

set_option autoImplicit true
open Function Set Stream'
open scoped Computability
attribute [local implicit_reducible] Stream'
attribute [local instance_reducible] Automata.DA.toNA Automata.DA.Prod
variable {A : Type}
theorem _root_.solution {I : Type} [Finite I] {s : Set I} {L : I → Set (Stream' A)}
    (h : ∀ i ∈ s, DetMullerLang (L i)) : DetMullerLang (⋃ i ∈ s, L i) := by
  generalize h_n : s.ncard = n
  induction' n with n h_ind generalizing s
  . obtain ⟨rfl⟩ := (ncard_eq_zero (s := s)).mp h_n
    simp +instances [det_muller_lang_empty]
  obtain ⟨i, t, h_i, rfl, rfl⟩ := (ncard_eq_succ (s := s)).mp h_n
  simp +instances ; apply det_muller_lang_union <;> grind
