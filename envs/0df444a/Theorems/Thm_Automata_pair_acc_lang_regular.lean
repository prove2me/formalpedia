-- Prove2me | Theorems.Thm_Automata_pair_acc_lang_regular
-- name    : Automata.pair_acc_lang_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:46:59.099235+00:00
-- url     : https://prove2.me/theorems/2ef62093-5013-4a8a-9e81-3f16db69f3b3
-- title:
--   Automata: pair acc lang regular
-- statement:
--   If `M` is finite-state, then `M.PairAccLang acc s s'` is regular for any pair of
--   states `s` and `s'`.  Note that we need to use the history NA construction to
--   prove this result, because the NA needs to remember whether an accepting state
--   has been visited.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Pair.lean#L287-L337
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Pair.lean#L287-L337

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

theorem Automata.pair_acc_lang_regular [Inhabited A] [h_fin : Finite M.State] {s s' : M.State} :
    RegLang (M.PairAccLang acc s s') := by sorry
