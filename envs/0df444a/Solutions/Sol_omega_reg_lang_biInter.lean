-- Prove2me | solution 1 for omega_reg_lang_biInter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:51:12.08802+00:00
-- url     : https://prove2.me/submissions/401ed702-d020-44a1-b974-2439634874b4

import Definitions.Def_AutomataTheory_Automata_OI2
import Definitions.Def_AutomataTheory_Congruences_BuchiCongr
import Definitions.Def_AutomataTheory_Languages_ChouekaLemma
import Definitions.Def_AutomataTheory_Languages_OmegaRegLang
import Theorems.Thm_omega_reg_lang_univ
import Theorems.Thm_omega_reg_lang_inter

set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream' Set.ncard
attribute [local instance_reducible] Automata.NA.OI2 Automata.NA.addHist Automata.NA.Prod
open Classical
variable {A : Type}
theorem _root_.solution {I : Type} [Finite I] {s : Set I} {L : I → Set (Stream' A)}
    (h : ∀ i ∈ s, OmegaRegLang (L i)) : OmegaRegLang (⋂ i ∈ s, L i) := by
  generalize h_n : s.ncard = n
  induction' n with n h_ind generalizing s
  . obtain ⟨rfl⟩ := (ncard_eq_zero (s := s)).mp h_n
    simp +instances [omega_reg_lang_univ]
  obtain ⟨i, t, h_i, rfl, rfl⟩ := (ncard_eq_succ (s := s)).mp h_n
  simp +instances ; apply omega_reg_lang_inter <;> grind
