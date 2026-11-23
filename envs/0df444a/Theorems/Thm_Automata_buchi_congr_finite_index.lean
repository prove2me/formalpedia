-- Prove2me | Theorems.Thm_Automata_buchi_congr_finite_index
-- name    : Automata.buchi_congr_finite_index
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:48:17.357331+00:00
-- url     : https://prove2.me/theorems/94378ff8-e30d-4343-8deb-f076431b9805
-- title:
--   Automata: buchi congr finite index
-- statement:
--   The BuchiCongr of an NA is of finite index if the NA is finite-state.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Congruences/BuchiCongr.lean#L150-L151
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Congruences/BuchiCongr.lean#L150-L151

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

theorem Automata.buchi_congr_finite_index [Finite M.State] : Finite (M.BuchiCongr acc).QuotType := by sorry
