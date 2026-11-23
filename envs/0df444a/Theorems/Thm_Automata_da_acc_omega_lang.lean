-- Prove2me | Theorems.Thm_Automata_da_acc_omega_lang
-- name    : Automata.da_acc_omega_lang
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:17:56.556836+00:00
-- url     : https://prove2.me/theorems/e3421a5e-6cc9-44a2-b0e8-f83f77b14d0d
-- title:
--   Automata: da acc omega lang
-- statement:
--   The ω-language accepted by a deterministic Buchi automaton is the ω-limit
--   of the language accepted by the same automaton.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Det.lean#L178-L200
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Det.lean#L178-L200

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Det
set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type} {M : DA A} {acc : Set M.State}

theorem Automata.da_acc_omega_lang :
    M.toNA.AcceptedOmegaLang acc = (M.toNA.AcceptedLang acc)↗ω := by sorry
