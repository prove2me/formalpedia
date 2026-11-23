-- Prove2me | Theorems.Thm_Automata_buchi_congr_ample
-- name    : Automata.buchi_congr_ample
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:48:33.884805+00:00
-- url     : https://prove2.me/theorems/0cc365db-d3a8-4250-ae90-6579362fb871
-- title:
--   Automata: buchi congr ample
-- statement:
--   The BuchiCongr of an NA is ample if the NA is finite-state.
--   For simplicity, this result is proved using a Ramsey theorem on infinite graphs.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Congruences/BuchiCongr.lean#L162-L191
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Congruences/BuchiCongr.lean#L162-L191

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

theorem Automata.buchi_congr_ample [Finite M.State] : (M.BuchiCongr acc).Ample := by sorry
