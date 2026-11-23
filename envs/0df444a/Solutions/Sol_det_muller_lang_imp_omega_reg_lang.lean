-- Prove2me | solution 1 for det_muller_lang_imp_omega_reg_lang
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:57:18.252445+00:00
-- url     : https://prove2.me/submissions/69255392-5859-4b68-a9af-2a647037250f

import Definitions.Def_AutomataTheory_Automata_DetConcat
import Definitions.Def_AutomataTheory_Automata_DetProd
import Definitions.Def_AutomataTheory_Languages_OmegaRegLang
import Definitions.Def_AutomataTheory_Languages_DetMullerLang
import Theorems.Thm_Automata_det_muller_accept_boolean_form
import Theorems.Thm_omega_reg_lang_biInter
import Theorems.Thm_omega_reg_lang_biUnion
import Theorems.Thm_omega_reg_lang_compl
import Theorems.Thm_omega_reg_lang_inter
import Theorems.Thm_omega_reg_lang_omega_limit


set_option autoImplicit true
open Function Set Stream'
open scoped Computability
attribute [local implicit_reducible] Stream'
attribute [local instance_reducible] Automata.DA.toNA Automata.DA.Prod
variable {A : Type}
theorem _root_.solution [Inhabited A] {L : Set (Stream' A)}
    (h : DetMullerLang L) : OmegaRegLang L := by
  obtain ⟨M, accSet, h_fin, rfl⟩ := h
  rw [Automata.det_muller_accept_boolean_form]
  have h_reg : ∀ s, RegLang (M.toNA.AcceptedLang {s}) := by
    intro s ; use M.toNA, {s} ; simp +instances [Automata.DA.toNA, h_fin]
  apply omega_reg_lang_biUnion ; intro acc h_acc
  apply omega_reg_lang_inter <;> apply omega_reg_lang_biInter <;> intro s h_s
  · apply omega_reg_lang_omega_limit
    exact h_reg s
  · apply omega_reg_lang_compl ; apply omega_reg_lang_omega_limit
    exact h_reg s
