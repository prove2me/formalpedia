-- Prove2me | Theorems.Thm_Automata_acc_lang_union
-- name    : Automata.acc_lang_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:29:14.019883+00:00
-- url     : https://prove2.me/theorems/cdf48b44-4973-4d80-9865-46fa3dee2915
-- title:
--   Automata: acc lang union
-- statement:
--   The language accepted by the sum NA is the union of the languages
--   accepted by the component automata.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Sum.lean#L129-L157
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Sum.lean#L129-L157

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Automata_Sum
set_option autoImplicit true
open Function Set Filter Stream'
attribute [local implicit_reducible] Stream'
open Automata
attribute [local instance_reducible] NA.Sum
variable {I A : Type} (M : I → NA A) (acc : (i : I) → Set ((M i).State))

theorem Automata.acc_lang_union :
    (NA.Sum M).AcceptedLang (NA.Sum_Acc M acc) = ⋃ i : I, (M i).AcceptedLang (acc i) := by sorry
