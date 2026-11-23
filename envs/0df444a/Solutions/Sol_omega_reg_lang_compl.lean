-- Prove2me | solution 1 for omega_reg_lang_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:56:22.991263+00:00
-- url     : https://prove2.me/submissions/1e7b32d9-31fd-4a93-96a1-7c0c719b0215

import Definitions.Def_AutomataTheory_Automata_OI2
import Definitions.Def_AutomataTheory_Congruences_BuchiCongr
import Definitions.Def_AutomataTheory_Languages_ChouekaLemma
import Definitions.Def_AutomataTheory_Languages_OmegaRegLang
import Theorems.Thm_omega_reg_lang_fin_idx_congr_compl
import Theorems.Thm_Automata_buchi_congr_ample
import Theorems.Thm_Automata_buchi_congr_finite_index
import Theorems.Thm_Automata_buchi_congr_saturates


set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream' Set.ncard
attribute [local instance_reducible] Automata.NA.OI2 Automata.NA.addHist Automata.NA.Prod
open Classical
variable {A : Type}
theorem _root_.solution [Inhabited A] {L : Set (Stream' A)}
    (h : OmegaRegLang L) : OmegaRegLang Lᶜ := by
  obtain ⟨M, acc, h_fin, rfl⟩ := h
  exact omega_reg_lang_fin_idx_congr_compl (c := M.BuchiCongr acc)
    Automata.buchi_congr_finite_index Automata.buchi_congr_ample Automata.buchi_congr_saturates
