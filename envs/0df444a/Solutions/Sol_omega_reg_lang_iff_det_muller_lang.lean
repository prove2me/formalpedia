-- Prove2me | solution 1 for omega_reg_lang_iff_det_muller_lang
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:58:22.989407+00:00
-- url     : https://prove2.me/submissions/f9e5d19a-e140-4e96-9093-c16706940f8d

import Definitions.Def_AutomataTheory_Automata_DetConcat
import Definitions.Def_AutomataTheory_Automata_DetProd
import Definitions.Def_AutomataTheory_Languages_OmegaRegLang
import Definitions.Def_AutomataTheory_Languages_DetMullerLang
import Theorems.Thm_det_muller_lang_imp_omega_reg_lang
import Theorems.Thm_omega_reg_lang_imp_det_muller_lang

set_option autoImplicit true
open Function Set Stream'
open scoped Computability
attribute [local implicit_reducible] Stream'
attribute [local instance_reducible] Automata.DA.toNA Automata.DA.Prod
variable {A : Type}
theorem _root_.solution [Inhabited A] {L : Set (Stream' A)} :
    OmegaRegLang L ↔ DetMullerLang L := by
  constructor
  · intro h ; exact omega_reg_lang_imp_det_muller_lang h
  · intro h ; exact det_muller_lang_imp_omega_reg_lang h
