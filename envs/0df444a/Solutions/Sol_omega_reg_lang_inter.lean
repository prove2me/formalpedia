-- Prove2me | solution 1 for omega_reg_lang_inter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:48:51.673918+00:00
-- url     : https://prove2.me/submissions/1bbaefbd-2d98-4dab-b316-751003afd5fd

import Definitions.Def_AutomataTheory_Automata_OI2
import Definitions.Def_AutomataTheory_Congruences_BuchiCongr
import Definitions.Def_AutomataTheory_Languages_ChouekaLemma
import Definitions.Def_AutomataTheory_Languages_OmegaRegLang
import Theorems.Thm_Automata_acc_omega_lang_inter2


set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream' Set.ncard
attribute [local instance_reducible] Automata.NA.OI2 Automata.NA.addHist Automata.NA.Prod
open Classical
variable {A : Type}
theorem _root_.solution {L0 L1 : Set (Stream' A)}
    (h0 : OmegaRegLang L0) (h1 : OmegaRegLang L1) : OmegaRegLang (L0 ∩ L1) := by
  obtain ⟨M0, acc0, h_fin0, h_l0⟩ := h0
  obtain ⟨M1, acc1, h_fin1, h_l1⟩ := h1
  let M_u : (i : Fin 2) → Automata.NA A
    | 0 => M0
    | 1 => M1
  let acc_u : (i : Fin 2) → Set (M_u i).State
    | 0 => acc0
    | 1 => acc1
  use (Automata.NA.OI2 M_u acc_u), (Automata.NA.OI2_Acc M_u acc_u)
  constructor
  · simp +instances [Automata.NA.OI2, Automata.NA.addHist, Automata.NA.Prod]
    have h_fin1 : ∀ i, Finite (M_u i).State := by simp +instances [Fin.forall_fin_two, M_u, h_fin0, h_fin1]
    have h_fin2 : Finite ((i : Fin 2) → (M_u i).State) := by exact Pi.finite
    exact Finite.instProd
  · ext as
    simp +instances [h_l0, h_l1, Automata.acc_omega_lang_inter2 M_u acc_u, Fin.forall_fin_two, M_u, acc_u]
