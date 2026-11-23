-- Prove2me | Theorems.Thm_Automata_acc_lang_concat_e
-- name    : Automata.acc_lang_concat_e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:25:18.589798+00:00
-- url     : https://prove2.me/theorems/ec3bdedc-35aa-4a2e-97f0-790669e62962
-- title:
--   Automata: acc lang concat e
-- statement:
--   The language of the concatenation NA that is accepted by `M0`'s accepting states
--   is the language accepted by `M0`.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Concat.lean#L289-L310
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Concat.lean#L289-L310

import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Automata_Concat
set_option autoImplicit true
open Function Set Filter Sum Stream'
open Classical
open Automata
variable {A : Type} {M0 M1 : NA A} {acc0 : Set M0.State} {acc1 : Set M1.State}

theorem Automata.acc_lang_concat_e :
    (M0.Concat acc0 M1).AcceptedLang (inl '' acc0) = M0.AcceptedLang acc0 := by sorry
