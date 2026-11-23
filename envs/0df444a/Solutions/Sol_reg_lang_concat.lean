-- Prove2me | solution 1 for reg_lang_concat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:45:15.61605+00:00
-- url     : https://prove2.me/submissions/a055f58f-ebd9-4d7c-9195-3e6e0ecd449b

import Definitions.Def_AutomataTheory_Automata_Sum
import Definitions.Def_AutomataTheory_Automata_Prod
import Definitions.Def_AutomataTheory_Automata_PSet
import Definitions.Def_AutomataTheory_Automata_Concat
import Definitions.Def_AutomataTheory_Automata_Loop
import Definitions.Def_AutomataTheory_Automata_Congr
import Definitions.Def_AutomataTheory_Languages_RegLang
import Theorems.Thm_reg_lang_concat_ne
import Theorems.Thm_reg_lang_concat_e

set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream'
open Classical
variable {A : Type}
theorem _root_.solution [Inhabited A] {L0 L1 : Set (List A)}
    (h0 : RegLang L0) (h1 : RegLang L1) : RegLang (L0 * L1) := by
  rcases Classical.em ([] ∈ L1) with h_e | h_ne
  · exact reg_lang_concat_e h0 h1 h_e
  . exact reg_lang_concat_ne h0 h1 h_ne
