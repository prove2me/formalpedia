-- Prove2me | Theorems.Thm_Automata_buchi_congr_saturates
-- name    : Automata.buchi_congr_saturates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:48:26.688858+00:00
-- url     : https://prove2.me/theorems/5f1bdbf9-f669-4fa7-9621-7ead155a7062
-- title:
--   Automata: buchi congr saturates
-- statement:
--   The BuchiCongr of an NA saturates the ω-language accepted by the NA.
--   Note that this result does not need to assume that the NA is finite-state.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Congruences/BuchiCongr.lean#L60-L109
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Congruences/BuchiCongr.lean#L60-L109

import Definitions.Def_AutomataTheory_Automata_Pair
import Definitions.Def_AutomataTheory_Mathlib_InfGraphRamsey
import Definitions.Def_AutomataTheory_Congruences_BuchiCongr
set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {A : Type}
variable {M : NA A} {acc : Set M.State}

theorem Automata.buchi_congr_saturates : (M.BuchiCongr acc).Saturates (M.AcceptedOmegaLang acc) := by sorry
