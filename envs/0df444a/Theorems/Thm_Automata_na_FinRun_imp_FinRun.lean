-- Prove2me | Theorems.Thm_Automata_na_FinRun_imp_FinRun
-- name    : Automata.na_FinRun_imp_FinRun
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:22:05.254321+00:00
-- url     : https://prove2.me/theorems/377bdc54-1ad8-4a96-99da-db04a9ef2bba
-- title:
--   Automata: na Fin Run imp Fin Run
-- statement:
--   The Automata construction uses the na Fin Run imp Fin Run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Basic.lean#L196-L198
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Basic.lean#L196-L198

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Automata_Basic
set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {A : Type} {M : NA A}

theorem Automata.na_FinRun_imp_FinRun {m n : ℕ} {as : Stream' A} {ss : Stream' M.State}
    (hmn : m < n) (hr : M.FinRun n as ss) : M.FinRun m as ss := by sorry
