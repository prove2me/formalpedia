-- Prove2me | Theorems.Thm_Automata_buchi_congr_param_surjective
-- name    : Automata.buchi_congr_param_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:48:23.140123+00:00
-- url     : https://prove2.me/theorems/f801a712-9014-460f-81d0-c95cc86c32c0
-- title:
--   Automata: buchi congr param surjective
-- statement:
--   BuchiCongrParam is a surjective map.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Congruences/BuchiCongr.lean#L134-L146
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Congruences/BuchiCongr.lean#L134-L146

import Definitions.Def_AutomataTheory_Automata_Pair
import Definitions.Def_AutomataTheory_Mathlib_InfGraphRamsey
import Definitions.Def_AutomataTheory_Congruences_BuchiCongr
set_option autoImplicit true
open Function Set Filter Stream'
open Automata
attribute [local instance_reducible] NA.BuchiCongr
open Classical
variable {A : Type}
variable {M : NA A} {acc : Set M.State}

theorem Automata.buchi_congr_param_surjective : Surjective (M.BuchiCongrParam acc) := by sorry
