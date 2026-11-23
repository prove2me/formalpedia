-- Prove2me | solution 1 for omega_reg_lang_fin_idx_congr_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:54:00.986693+00:00
-- url     : https://prove2.me/submissions/753cf810-b91e-431a-8fc5-9da0d088b1a0

import Definitions.Def_AutomataTheory_Automata_OI2
import Definitions.Def_AutomataTheory_Congruences_BuchiCongr
import Definitions.Def_AutomataTheory_Languages_ChouekaLemma
import Definitions.Def_AutomataTheory_Languages_OmegaRegLang
import Theorems.Thm_omega_reg_lang_fin_idx_congr
import Theorems.Thm_congruence_saturates_compl


set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream' Set.ncard
attribute [local instance_reducible] Automata.NA.OI2 Automata.NA.addHist Automata.NA.Prod
open Classical
variable {A : Type}
theorem _root_.solution [Inhabited A] {c : Congruence A} {L : Set (Stream' A)}
    (h_fin : Finite (c.QuotType)) (h_amp : c.Ample) (h_sat : c.Saturates L) : OmegaRegLang Lᶜ := by
  have h_sat' := congruence_saturates_compl h_sat
  exact omega_reg_lang_fin_idx_congr h_fin h_amp h_sat'
