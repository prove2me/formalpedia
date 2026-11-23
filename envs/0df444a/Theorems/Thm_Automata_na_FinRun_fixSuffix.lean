-- Prove2me | Theorems.Thm_Automata_na_FinRun_fixSuffix
-- name    : Automata.na_FinRun_fixSuffix
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:22:03.829002+00:00
-- url     : https://prove2.me/theorems/255a7b25-f5c6-4322-9955-ad012926bb5e
-- title:
--   Automata: na Fin Run fix Suffix
-- statement:
--   The Automata construction uses the na Fin Run fix Suffix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Basic.lean#L180-L187
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Basic.lean#L180-L187

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Automata_Basic
set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {A : Type} {M : NA A}

theorem Automata.na_FinRun_fixSuffix [Inhabited A] {n : ℕ} {as : Stream' A} {ss : Stream' M.State}
    (h : M.FinRun n as ss) : M.FinRun n (fixSuffix as n default) (fixSuffix ss (n + 1) (ss 0)) := by sorry
