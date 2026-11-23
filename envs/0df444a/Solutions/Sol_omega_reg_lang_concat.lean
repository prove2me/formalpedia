-- Prove2me | solution 1 for omega_reg_lang_concat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:50:29.562803+00:00
-- url     : https://prove2.me/submissions/56280b85-790b-4d44-9268-abc12b85976f

import Definitions.Def_AutomataTheory_Automata_OI2
import Definitions.Def_AutomataTheory_Congruences_BuchiCongr
import Definitions.Def_AutomataTheory_Languages_ChouekaLemma
import Definitions.Def_AutomataTheory_Languages_OmegaRegLang
import Theorems.Thm_Automata_acc_omega_lang_concat


set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream' Set.ncard
attribute [local instance_reducible] Automata.NA.OI2 Automata.NA.addHist Automata.NA.Prod
open Classical
variable {A : Type}
theorem _root_.solution {L0 : Set (List A)} {L1 : Set (Stream' A)}
    (h0 : RegLang L0) (h1 : OmegaRegLang L1) : OmegaRegLang (L0 * L1) := by
  obtain ⟨M0, acc0, h_fin0, h_l0⟩ := h0
  obtain ⟨M1, acc1, h_fin1, h_l1⟩ := h1
  use (M0.Concat acc0 M1), (inr '' acc1)
  constructor
  · exact Finite.instSum
  · simp +instances [h_l0, h_l1, Automata.acc_omega_lang_concat]
