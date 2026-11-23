-- Prove2me | solution 1 for omega_reg_lang_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:50:19.110231+00:00
-- url     : https://prove2.me/submissions/96c1546a-99f1-4a40-b14c-69d0b5116c9d

import Definitions.Def_AutomataTheory_Automata_OI2
import Definitions.Def_AutomataTheory_Congruences_BuchiCongr
import Definitions.Def_AutomataTheory_Languages_ChouekaLemma
import Definitions.Def_AutomataTheory_Languages_OmegaRegLang

set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream' Set.ncard
attribute [local instance_reducible] Automata.NA.OI2 Automata.NA.addHist Automata.NA.Prod
open Classical
variable {A : Type}
theorem _root_.solution :
    OmegaRegLang (∅ : Set (Stream' A)) := by
  let M := Automata.NA.mk (A := A) Unit ∅ (fun _ _ ↦ ∅)
  use M, ∅ ; constructor
  · exact Finite.of_fintype Unit
  ext as ; simp +instances [Automata.NA.AcceptedOmegaLang, Automata.NA.BuchiAccept]
