-- Prove2me | Theorems.Thm_Automata_det_muller_accept_boolean_form
-- name    : Automata.det_muller_accept_boolean_form
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:26:31.114727+00:00
-- url     : https://prove2.me/theorems/eca9302d-1004-446f-8253-a9a340a1270d
-- title:
--   Automata: det muller accept boolean form
-- statement:
--   The ω-language accepted by a deterministic Muller automaton is a boolean
--   combination of the ω-limits of accepted languages.  Note that this result does
--   not need to assume that the automaton is finite-state.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Det.lean#L243-L268
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Det.lean#L243-L268

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Det
set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type}

theorem Automata.det_muller_accept_boolean_form (M : DA A) (accSet : Set (Set M.State)) :
    {as | M.MullerAccept accSet as} =
    ⋃ acc ∈ accSet, (⋂ s ∈ acc, (M.toNA.AcceptedLang {s})↗ω) ∩ (⋂ s ∈ accᶜ, ((M.toNA.AcceptedLang {s})↗ω)ᶜ) := by sorry
