-- Prove2me | Theorems.Thm_Automata_det_muller_accept_compl
-- name    : Automata.det_muller_accept_compl
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:26:11.265883+00:00
-- url     : https://prove2.me/theorems/be4da118-e46f-4066-9182-47e262348ab8
-- title:
--   Automata: det muller accept compl
-- statement:
--   For a deterministic Muller automaton, complementing the ω-language it accepts
--   can be achieved by simply complementing the set of accepting state sets.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Det.lean#L216-L218
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Det.lean#L216-L218

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Det
set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type}

theorem Automata.det_muller_accept_compl (M : DA A) (accSet : Set (Set M.State)) (as : Stream' A) :
    M.MullerAccept accSetᶜ as ↔ ¬ M.MullerAccept accSet as := by sorry
