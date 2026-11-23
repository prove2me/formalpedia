-- Prove2me | Theorems.Thm_Automata_na_pset_run
-- name    : Automata.na_pset_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:29:16.70564+00:00
-- url     : https://prove2.me/theorems/df2086e6-5281-4fd3-a13e-283985ab4b4c
-- title:
--   Automata: na pset run
-- statement:
--   For any input `as`, running `M.Pset` on `as` ends in the unique state
--   that is exact the set of states reachable by running `M` on `as`.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/PSet.lean#L53-L78
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/PSet.lean#L53-L78

import Definitions.Def_AutomataTheory_Automata_Det
import Definitions.Def_AutomataTheory_Automata_PSet
set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type}
attribute [local instance_reducible] NA.PSet
variable {M : NA A}

theorem Automata.na_pset_run (as : Stream' A) (k : ℕ) :
    M.PSet.DetRun as k = { s : M.State | ∃ ss, M.FinRun k as ss ∧ ss k = s } := by sorry
