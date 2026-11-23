-- Prove2me | Theorems.Thm_Automata_acc_lang_loop_concat
-- name    : Automata.acc_lang_loop_concat
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:28:04.664799+00:00
-- url     : https://prove2.me/theorems/5328953d-7f9b-4cf1-97c1-ca1946cd5062
-- title:
--   Automata: acc lang loop concat
-- statement:
--   The concatenation of the language accepted by the loop NA with itself
--   is a subset of itself.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Loop.lean#L163-L194
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Loop.lean#L163-L194

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

theorem Automata.acc_lang_loop_concat :
    ((M.Loop acc).AcceptedLang {inl ()}) * ((M.Loop acc).AcceptedLang {inl ()}) ⊆
    (M.Loop acc).AcceptedLang {inl ()} := by sorry
