-- Prove2me | solution 1 for det_muller_lang_omega_limit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:52:13.220571+00:00
-- url     : https://prove2.me/submissions/ca232719-fda3-4a54-bf90-4197cd80931f

import Definitions.Def_AutomataTheory_Automata_DetConcat
import Definitions.Def_AutomataTheory_Automata_DetProd
import Definitions.Def_AutomataTheory_Languages_OmegaRegLang
import Definitions.Def_AutomataTheory_Languages_DetMullerLang
import Theorems.Thm_Automata_det_muller_accept_omega_limit
import Theorems.Thm_reg_lang_det_accept


set_option autoImplicit true
open Function Set Stream'
open scoped Computability
attribute [local implicit_reducible] Stream'
attribute [local instance_reducible] Automata.DA.toNA Automata.DA.Prod
variable {A : Type}
theorem _root_.solution {L : Set (List A)}
    (h : RegLang L) : DetMullerLang L↗ω := by
  obtain ⟨M, acc, h_fin, rfl⟩ := reg_lang_det_accept h
  obtain ⟨accSet, h_acc⟩ := Automata.det_muller_accept_omega_limit M acc
  use M, accSet
