-- Prove2me | solution 1 for det_muller_lang_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:51:20.373695+00:00
-- url     : https://prove2.me/submissions/f0b0e3d3-8f20-40e8-8284-3b4329871263

import Definitions.Def_AutomataTheory_Automata_DetConcat
import Definitions.Def_AutomataTheory_Automata_DetProd
import Definitions.Def_AutomataTheory_Languages_OmegaRegLang
import Definitions.Def_AutomataTheory_Languages_DetMullerLang

set_option autoImplicit true
open Function Set Stream'
open scoped Computability
attribute [local implicit_reducible] Stream'
attribute [local instance_reducible] Automata.DA.toNA Automata.DA.Prod
variable {A : Type}
theorem _root_.solution :
    DetMullerLang (univ : Set (Stream' A)) := by
  let M := Automata.DA.mk (A := A) Unit () (fun _ _ ↦ ())
  use M, {{()}} ; constructor
  · exact Finite.of_fintype Unit
  ext as ; simp +instances [Automata.DA.MullerAccept]
  have h : M.DetRun as = fun _ ↦ () := by
    funext k
    exact @Subsingleton.elim Unit inferInstance _ _
  ext s ; simp +instances [h, InfOcc]
