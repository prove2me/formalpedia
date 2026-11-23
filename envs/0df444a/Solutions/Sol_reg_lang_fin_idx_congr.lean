-- Prove2me | solution 1 for reg_lang_fin_idx_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:44:22.064126+00:00
-- url     : https://prove2.me/submissions/d252315a-573a-4c6b-8976-58404269ed26

import Definitions.Def_AutomataTheory_Automata_Sum
import Definitions.Def_AutomataTheory_Automata_Prod
import Definitions.Def_AutomataTheory_Automata_PSet
import Definitions.Def_AutomataTheory_Automata_Concat
import Definitions.Def_AutomataTheory_Automata_Loop
import Definitions.Def_AutomataTheory_Automata_Congr
import Definitions.Def_AutomataTheory_Languages_RegLang
import Theorems.Thm_acc_lang_congr


set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream'
open Classical
variable {A : Type}
theorem _root_.solution [Inhabited A] {c : Congruence A}
    (h : Finite (c.QuotType)) (s : c.QuotType) : RegLang (c.EqvCls s) := by
  use c.toDA.toNA, {s}
  constructor
  · exact h
  · exact acc_lang_congr s
