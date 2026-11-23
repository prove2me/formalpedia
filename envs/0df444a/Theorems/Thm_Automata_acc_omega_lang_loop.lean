-- Prove2me | Theorems.Thm_Automata_acc_omega_lang_loop
-- name    : Automata.acc_omega_lang_loop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:28:18.162804+00:00
-- url     : https://prove2.me/theorems/b20c566c-54b9-45f8-9267-4b57c89f6e09
-- title:
--   Automata: acc omega lang loop
-- statement:
--   The ω-language accepted by the loop NA is the ω-power of
--   the language accepted by `M`.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Loop.lean#L272-L345
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Loop.lean#L272-L345

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

theorem Automata.acc_omega_lang_loop :
    (M.Loop acc).AcceptedOmegaLang {inl ()} = (M.AcceptedLang acc)^ω := by sorry
