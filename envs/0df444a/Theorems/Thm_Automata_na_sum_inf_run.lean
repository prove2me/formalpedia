-- Prove2me | Theorems.Thm_Automata_na_sum_inf_run
-- name    : Automata.na_sum_inf_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:29:11.754705+00:00
-- url     : https://prove2.me/theorems/7dbae702-9b50-4655-aea9-ec4d86929162
-- title:
--   Automata: na sum inf run
-- statement:
--   The Automata construction uses the na sum inf run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Sum.lean#L76-L114
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Sum.lean#L76-L114

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Automata_Sum
set_option autoImplicit true
open Function Set Filter Stream'
attribute [local implicit_reducible] Stream'
open Automata
variable {I A : Type}
attribute [local instance_reducible] NA.Sum
variable {M : I → NA A}

theorem Automata.na_sum_inf_run {as : Stream' A} {ss : Stream' (NA.Sum M).State} :
    (NA.Sum M).InfRun as ss ↔ ∃ i ss_i, (M i).InfRun as ss_i ∧ ss = (Sigma.mk i) ∘ ss_i := by sorry
