-- Prove2me | Theorems.Thm_Automata_det_muller_accept_union
-- name    : Automata.det_muller_accept_union
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:28:05.194916+00:00
-- url     : https://prove2.me/theorems/2ca4b857-5f29-48bd-a3a8-547d78c49aa0
-- title:
--   Automata: det muller accept union
-- statement:
--   The Automata construction uses the det muller accept union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/DetProd.lean#L66-L73
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/DetProd.lean#L66-L73

import Definitions.Def_AutomataTheory_Automata_Det
import Definitions.Def_AutomataTheory_Automata_DetProd
set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {I A : Type}
variable (M : I → DA A)
variable [Finite I] [∀ i, Finite (M i).State]
variable (accSet : (i : I) → Set (Set (M i).State))

theorem Automata.det_muller_accept_union (as : Stream' A) :
    (DA.Prod M).MullerAccept (DA.MullerAcc_Union M accSet) as ↔
    ∃ i : I, (M i).MullerAccept (accSet i) as := by sorry
