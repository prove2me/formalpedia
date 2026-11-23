-- Prove2me | Theorems.Thm_Automata_acc_omega_lang_concat
-- name    : Automata.acc_omega_lang_concat
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:25:22.786279+00:00
-- url     : https://prove2.me/theorems/cbe351bf-089d-45db-a6d6-9997c589c316
-- title:
--   Automata: acc omega lang concat
-- statement:
--   The ω-language of the concatenation NA that is accepted by `M1`'s accepting states
--   is the language accepted by `M0` concatenated with the ω-language accepted by `M1`.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Concat.lean#L372-L418
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Concat.lean#L372-L418

import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Automata_Concat
set_option autoImplicit true
open Function Set Filter Sum Stream'
open Classical
open Automata
variable {A : Type} {M0 M1 : NA A} {acc0 : Set M0.State} {acc1 : Set M1.State}

theorem Automata.acc_omega_lang_concat :
    (M0.Concat acc0 M1).AcceptedOmegaLang (inr '' acc1) =
    (M0.AcceptedLang acc0) * (M1.AcceptedOmegaLang acc1) := by sorry
