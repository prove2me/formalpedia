-- Prove2me | solution 1 for det_muller_lang_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:53:54.247451+00:00
-- url     : https://prove2.me/submissions/d6e51c18-cd90-4377-a870-35775be08cf8

import Definitions.Def_AutomataTheory_Automata_DetConcat
import Definitions.Def_AutomataTheory_Automata_DetProd
import Definitions.Def_AutomataTheory_Languages_OmegaRegLang
import Definitions.Def_AutomataTheory_Languages_DetMullerLang
import Theorems.Thm_Automata_det_muller_accept_compl


set_option autoImplicit true
open Function Set Stream'
open scoped Computability
attribute [local implicit_reducible] Stream'
attribute [local instance_reducible] Automata.DA.toNA Automata.DA.Prod
variable {A : Type}
theorem _root_.solution {L : Set (Stream' A)}
    (h : DetMullerLang L) : DetMullerLang Lᶜ := by
  obtain ⟨M, accSet, h_fin, rfl⟩ := h
  use M, accSetᶜ ; constructor
  · exact h_fin
  · ext as ; simp +instances [Automata.det_muller_accept_compl]
