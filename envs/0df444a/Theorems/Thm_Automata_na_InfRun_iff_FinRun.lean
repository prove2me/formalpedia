-- Prove2me | Theorems.Thm_Automata_na_InfRun_iff_FinRun
-- name    : Automata.na_InfRun_iff_FinRun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:18:41.478203+00:00
-- url     : https://prove2.me/theorems/282609b0-59d9-4ee9-8041-6add921d1f59
-- title:
--   Automata: na Inf Run iff Fin Run
-- statement:
--   The Automata construction uses the na Inf Run iff Fin Run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Basic.lean#L200-L212
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Basic.lean#L200-L212

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Automata_Basic
set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {A : Type} {M : NA A}

theorem Automata.na_InfRun_iff_FinRun {as : Stream' A} {ss : Stream' M.State} :
    M.InfRun as ss ↔ ∀ n, M.FinRun n as ss := by sorry
