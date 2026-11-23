-- Prove2me | solution 1 for omega_reg_lang_omega_iter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:50:58.753703+00:00
-- url     : https://prove2.me/submissions/a651ff7e-6934-48ee-9a24-eb6881ccdf70

import Definitions.Def_AutomataTheory_Automata_OI2
import Definitions.Def_AutomataTheory_Congruences_BuchiCongr
import Definitions.Def_AutomataTheory_Languages_ChouekaLemma
import Definitions.Def_AutomataTheory_Languages_OmegaRegLang
import Theorems.Thm_Automata_acc_omega_lang_loop


set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream' Set.ncard
attribute [local instance_reducible] Automata.NA.OI2 Automata.NA.addHist Automata.NA.Prod
open Classical
variable {A : Type}
theorem _root_.solution {L : Set (List A)}
    (h : RegLang L) : OmegaRegLang L^ω := by
  obtain ⟨M, acc, h_fin, h_l⟩ := h
  use (M.Loop acc), {inl ()}
  constructor
  · exact Finite.instSum
  · simp +instances [h_l, Automata.acc_omega_lang_loop]
