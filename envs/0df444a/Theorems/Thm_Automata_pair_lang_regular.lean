-- Prove2me | Theorems.Thm_Automata_pair_lang_regular
-- name    : Automata.pair_lang_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:31:33.929392+00:00
-- url     : https://prove2.me/theorems/68d70e25-d04f-4dc1-b6c7-95d8dcef0cda
-- title:
--   Automata: pair lang regular
-- statement:
--   If `M` is finite-state, then `M.PairLang s s'` is regular for any pair of
--   states `s` and `s'`.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Pair.lean#L267-L280
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Pair.lean#L267-L280

import Definitions.Def_AutomataTheory_Automata_Hist
import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Pair
set_option autoImplicit true
open Function Set Filter Stream'
attribute [local implicit_reducible] Stream'
open Automata
attribute [local instance_reducible] NA.addHist
variable {A : Type}
variable {M : NA A} {acc : Set M.State}
attribute [local instance_reducible] NA.SingleInit

theorem Automata.pair_lang_regular [Inhabited A] [h_fin : Finite M.State] {s s' : M.State} :
    RegLang (M.PairLang s s') := by sorry
