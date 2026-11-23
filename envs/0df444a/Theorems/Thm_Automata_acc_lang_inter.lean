-- Prove2me | Theorems.Thm_Automata_acc_lang_inter
-- name    : Automata.acc_lang_inter
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:28:31.014073+00:00
-- url     : https://prove2.me/theorems/264d5fcb-5945-46ee-a664-bc409388dc9f
-- title:
--   Automata: acc lang inter
-- statement:
--   The language accepted by the product NA is the intersection of the languages
--   accepted by the component automata.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Prod.lean#L67-L93
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Prod.lean#L67-L93

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Automata_Prod
set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {I A : Type} (M : I → NA A) (acc : (i : I) → Set ((M i).State))

theorem Automata.acc_lang_inter [Inhabited A] :
    (NA.Prod M).AcceptedLang (NA.Prod_Acc M acc) = ⋂ i : I, (M i).AcceptedLang (acc i) := by sorry
