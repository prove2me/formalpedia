-- Prove2me | Theorems.Thm_Automata_acc_lang_loop
-- name    : Automata.acc_lang_loop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:28:11.345473+00:00
-- url     : https://prove2.me/theorems/9c7f08dc-79b5-408c-81c0-9ef8e09ae2d1
-- title:
--   Automata: acc lang loop
-- statement:
--   The language accepted by the loop NA is the Kleene star of
--   the language accepted by `M`.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Loop.lean#L199-L267
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Loop.lean#L199-L267

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Automata_Loop
set_option autoImplicit true
open Function Set Sum Filter Stream'
open Classical
open scoped Computability
attribute [local instance_reducible] Stream'
open Automata
attribute [local instance_reducible] NA.Loop
variable {A : Type} {M : NA A} {acc : Set M.State}

theorem Automata.acc_lang_loop [Inhabited A] :
    (M.Loop acc).AcceptedLang {inl ()} = (M.AcceptedLang acc)∗ := by sorry
