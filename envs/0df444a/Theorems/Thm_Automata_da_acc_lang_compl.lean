-- Prove2me | Theorems.Thm_Automata_da_acc_lang_compl
-- name    : Automata.da_acc_lang_compl
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:26:01.308391+00:00
-- url     : https://prove2.me/theorems/af232d6b-80aa-4e58-9541-a9ef4cfa56ff
-- title:
--   Automata: da acc lang compl
-- statement:
--   For a `DA`, complementing the language it accepts can be achieved
--   by simply complementing the set of accepting states.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Det.lean#L139-L173
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Det.lean#L139-L173

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Det
set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type} {M : DA A} {acc : Set M.State}

theorem Automata.da_acc_lang_compl [Inhabited A] :
    M.toNA.AcceptedLang accᶜ = (M.toNA.AcceptedLang acc)ᶜ := by sorry
