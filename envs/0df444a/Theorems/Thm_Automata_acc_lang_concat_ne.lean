-- Prove2me | Theorems.Thm_Automata_acc_lang_concat_ne
-- name    : Automata.acc_lang_concat_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:19:25.851528+00:00
-- url     : https://prove2.me/theorems/d86d95be-4f62-412b-aa9b-afb6739bf2e6
-- title:
--   Automata: acc lang concat ne
-- statement:
--   The language of the concatenation NA that is accepted by `M1`'s accepting states
--   is the language accepted by `M0` concatenated with the language accepted by `M1` minus
--   the empty word.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Concat.lean#L316-L367
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Concat.lean#L316-L367

import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Automata_Concat
set_option autoImplicit true
open Function Set Filter Sum Stream'
open Classical
open Automata
variable {A : Type} {M0 M1 : NA A} {acc0 : Set M0.State} {acc1 : Set M1.State}

theorem Automata.acc_lang_concat_ne :
    (M0.Concat acc0 M1).AcceptedLang (inr '' acc1) =
    (M0.AcceptedLang acc0) * (M1.AcceptedLang acc1 \ {[]}) := by sorry
