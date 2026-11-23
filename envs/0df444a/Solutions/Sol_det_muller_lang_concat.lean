-- Prove2me | solution 1 for det_muller_lang_concat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:52:20.053799+00:00
-- url     : https://prove2.me/submissions/a726c678-6482-46da-af3a-ea2b79f202ae

import Definitions.Def_AutomataTheory_Automata_DetConcat
import Definitions.Def_AutomataTheory_Automata_DetProd
import Definitions.Def_AutomataTheory_Languages_OmegaRegLang
import Definitions.Def_AutomataTheory_Languages_DetMullerLang
import Theorems.Thm_Automata_da_concat_of_muller_accept
import Theorems.Thm_Automata_da_concat_to_muller_accept
import Theorems.Thm_P2M_Stream__append_extract_drop_29d8f2c46a9f
import Theorems.Thm_P2M_Stream__get_append_left__364c5eb8ed49
import Theorems.Thm_P2M_Stream__get_extract__ebf059d6908b
import Theorems.Thm_reg_lang_det_accept


set_option autoImplicit true
open Function Set Stream'
open scoped Computability
attribute [local implicit_reducible] Stream'
attribute [local instance_reducible] Automata.DA.toNA Automata.DA.Prod
variable {A : Type}
theorem _root_.solution {L0 : Set (List A)} {L1 : Set (Stream' A)}
    (h0 : RegLang L0) (h1 : DetMullerLang L1) : DetMullerLang (L0 * L1) := by
  obtain ⟨M0, acc0, h_fin0, rfl⟩ := reg_lang_det_accept h0
  obtain ⟨M1, accSet1, h_fin1, rfl⟩ := h1
  use (M0.Concat acc0 M1), (Automata.DA.MullerAcc_Concat M0 acc0 M1 accSet1)
  constructor
  · apply Finite.instProd
  · ext as ; constructor
    · intro h_acc
      obtain ⟨n, h_acc0, h_acc1⟩ := Automata.da_concat_of_muller_accept M0 acc0 M1 accSet1 as h_acc
      use (as.extract 0 n), (as.drop n)
      simp +instances [h_acc1, append_extract_drop]
      use n, as
    · rintro ⟨al0, as1, ⟨n, as0, h_as0, rfl⟩, h_as1, h_as⟩
      have h_acc0 : M0.toNA.FinAccept acc0 n as := by
        obtain ⟨ss0, h_run0, h_acc0⟩ := h_as0
        use ss0 ; simp +instances [← h_as, h_acc0] ; constructor
        · exact h_run0.1
        intro k h_k
        have h1 : k < (as0.extract 0 n).length := by simp +instances [length_extract, h_k]
        simp +instances (disch := omega) [get_append_left' h1, get_extract', h_run0.2 k h_k]
      have h_acc1 : M1.MullerAccept accSet1 (as.drop n) := by
        have h1 : n = (as0.extract 0 n).length := by simp +instances [length_extract]
        rw [h1] ; simp +instances [← h_as, drop_append_stream] ; exact h_as1
      exact Automata.da_concat_to_muller_accept M0 acc0 M1 accSet1 as n h_acc0 h_acc1
