-- Prove2me | solution 1 for det_muller_lang_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:51:02.599121+00:00
-- url     : https://prove2.me/submissions/2c0a0091-05bf-42c1-a247-a2fd65c25c75

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
    DetMullerLang (∅ : Set (Stream' A)) := by
  let M := Automata.DA.mk (A := A) Unit () (fun _ _ ↦ ())
  use M, ∅ ; constructor
  · exact Finite.of_fintype Unit
  ext as ; simp +instances [Automata.DA.MullerAccept]
