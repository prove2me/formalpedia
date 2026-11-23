-- Prove2me | solution 1 for omega_reg_lang_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:50:26.719069+00:00
-- url     : https://prove2.me/submissions/2c5bbbac-13f3-43cd-9a3a-ebff7e9670f9

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
    OmegaRegLang (univ : Set (Stream' A)) := by
  let M := Automata.NA.mk (A := A) Unit {()} (fun _ _ ↦ {()})
  use M, {()} ; constructor
  · exact Finite.of_fintype Unit
  ext as ; simp +instances [Automata.NA.AcceptedOmegaLang, Automata.NA.BuchiAccept]
  use (fun _ ↦ ()) ; constructor
  · simp +instances [Automata.NA.InfRun, M]
  · simp +instances [atTop_neBot]
