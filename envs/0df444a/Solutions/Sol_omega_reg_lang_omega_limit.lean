-- Prove2me | solution 1 for omega_reg_lang_omega_limit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:50:59.239745+00:00
-- url     : https://prove2.me/submissions/13128608-aa6c-449b-bc76-b96ba110a994

import Definitions.Def_AutomataTheory_Automata_OI2
import Definitions.Def_AutomataTheory_Congruences_BuchiCongr
import Definitions.Def_AutomataTheory_Languages_ChouekaLemma
import Definitions.Def_AutomataTheory_Languages_OmegaRegLang
import Theorems.Thm_Automata_da_acc_omega_lang
import Theorems.Thm_reg_lang_det_accept


set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream' Set.ncard
attribute [local instance_reducible] Automata.NA.OI2 Automata.NA.addHist Automata.NA.Prod
open Classical
variable {A : Type}
theorem _root_.solution {L : Set (List A)}
    (h : RegLang L) : OmegaRegLang L↗ω := by
  obtain ⟨M, acc, h_fin, rfl⟩ := reg_lang_det_accept h
  use M.toNA, acc ; constructor
  · exact h_fin
  · exact Automata.da_acc_omega_lang
