-- Prove2me | Theorems.Thm_Automata_acc_lang_acc_union
-- name    : Automata.acc_lang_acc_union
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:22:26.7045+00:00
-- url     : https://prove2.me/theorems/59c874eb-3a9f-41e3-b89e-6658639b952e
-- title:
--   Automata: acc lang acc union
-- statement:
--   The Automata construction uses the acc lang acc union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Basic.lean#L214-L222
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Basic.lean#L214-L222

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Automata_Basic
set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {A : Type} {M : NA A}

theorem Automata.acc_lang_acc_union {acc0 acc1 : Set M.State} :
    M.AcceptedLang (acc0 ∪ acc1) = M.AcceptedLang acc0 ∪ M.AcceptedLang acc1 := by sorry
