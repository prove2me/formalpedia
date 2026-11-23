-- Prove2me | Theorems.Thm_Automata_det_muller_accept_omega_limit
-- name    : Automata.det_muller_accept_omega_limit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:26:26.682269+00:00
-- url     : https://prove2.me/theorems/8f3468a1-3be9-4f92-b4e6-25c6b68fc12f
-- title:
--   Automata: det muller accept omega limit
-- statement:
--   The ω-limit of the language accepted by a deterministic automaton is
--   accepted by a deterministic Muller automaton.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Det.lean#L223-L237
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Det.lean#L223-L237

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Det
set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type}

theorem Automata.det_muller_accept_omega_limit (M : DA A) [Finite M.State] (acc : Set M.State) :
    ∃ accSet, {as | M.MullerAccept accSet as} = (M.toNA.AcceptedLang acc)↗ω := by sorry
