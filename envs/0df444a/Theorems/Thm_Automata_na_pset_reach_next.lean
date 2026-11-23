-- Prove2me | Theorems.Thm_Automata_na_pset_reach_next
-- name    : Automata.na_pset_reach_next
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:29:03.01881+00:00
-- url     : https://prove2.me/theorems/d1a64888-35ec-4e83-9590-845a8507b641
-- title:
--   Automata: na pset reach next
-- statement:
--   The Automata construction uses the na pset reach next property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/PSet.lean#L46-L48
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/PSet.lean#L46-L48

import Definitions.Def_AutomataTheory_Automata_Det
import Definitions.Def_AutomataTheory_Automata_PSet
set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type}
attribute [local instance_reducible] NA.PSet
variable {M : NA A}

theorem Automata.na_pset_reach_next (as : Stream' A) (k : ℕ) :
    M.PSet.DetRun as (k + 1) = ⋃ s ∈ M.PSet.DetRun as k, M.next s (as k) := by sorry
