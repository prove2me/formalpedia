-- Prove2me | Theorems.Thm_Automata_acc_omega_lang_union
-- name    : Automata.acc_omega_lang_union
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:29:10.428026+00:00
-- url     : https://prove2.me/theorems/0374b7f4-21e4-44d9-a51c-bdd6ea109a3e
-- title:
--   Automata: acc omega lang union
-- statement:
--   The ω-language accepted by the sum NA is the union of the ω-languages
--   accepted by the component automata.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Sum.lean#L162-L193
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Sum.lean#L162-L193

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Automata_Sum
set_option autoImplicit true
open Function Set Filter Stream'
attribute [local implicit_reducible] Stream'
open Automata
attribute [local instance_reducible] NA.Sum
variable {I A : Type} (M : I → NA A) (acc : (i : I) → Set ((M i).State))

theorem Automata.acc_omega_lang_union :
    (NA.Sum M).AcceptedOmegaLang (NA.Sum_Acc M acc) = ⋃ i : I, (M i).AcceptedOmegaLang (acc i) := by sorry
