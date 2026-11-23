-- Prove2me | solution 1 for omega_reg_lang_imp_det_muller_lang
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:56:32.087191+00:00
-- url     : https://prove2.me/submissions/ff9aabb2-bbc6-4d10-b6fa-99592320b370

import Definitions.Def_AutomataTheory_Automata_DetConcat
import Definitions.Def_AutomataTheory_Automata_DetProd
import Definitions.Def_AutomataTheory_Languages_OmegaRegLang
import Definitions.Def_AutomataTheory_Languages_DetMullerLang
import Theorems.Thm_det_muller_lang_biUnion
import Theorems.Thm_det_muller_lang_omega_limit
import Theorems.Thm_det_muller_lang_concat
import Theorems.Thm_choueka_lemma
import Theorems.Thm_omega_reg_lang_iff_finite_union_form
import Theorems.Thm_reg_lang_iter


set_option autoImplicit true
open Function Set Stream'
open scoped Computability
attribute [local implicit_reducible] Stream'
attribute [local instance_reducible] Automata.DA.toNA Automata.DA.Prod
variable {A : Type}
theorem _root_.solution [Inhabited A] {L : Set (Stream' A)}
    (h : OmegaRegLang L) : DetMullerLang L := by
  obtain ⟨n, U, V, h_reg, rfl⟩ := omega_reg_lang_iff_finite_union_form.mp h
  rw [← biUnion_univ] ; apply det_muller_lang_biUnion
  intro i _ ; apply det_muller_lang_concat
  · exact (h_reg i).1
  · have h_v := (h_reg i).2
    obtain ⟨W, h_w, h_omega⟩ := choueka_lemma h_v
    rw [h_omega] ; apply det_muller_lang_concat
    · exact reg_lang_iter h_v
    · exact det_muller_lang_omega_limit h_w
