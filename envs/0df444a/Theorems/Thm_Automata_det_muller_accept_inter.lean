-- Prove2me | Theorems.Thm_Automata_det_muller_accept_inter
-- name    : Automata.det_muller_accept_inter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:28:02.084598+00:00
-- url     : https://prove2.me/theorems/fe5d5e76-2660-4ed5-b65e-5e523563b0b3
-- title:
--   Automata: det muller accept inter
-- statement:
--   The Automata construction uses the det muller accept inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/DetProd.lean#L57-L64
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/DetProd.lean#L57-L64

import Definitions.Def_AutomataTheory_Automata_Det
import Definitions.Def_AutomataTheory_Automata_DetProd
set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {I A : Type}
variable (M : I → DA A)
variable [Finite I] [∀ i, Finite (M i).State]
variable (accSet : (i : I) → Set (Set (M i).State))

theorem Automata.det_muller_accept_inter (as : Stream' A) :
    (DA.Prod M).MullerAccept (DA.MullerAcc_Inter M accSet) as ↔
    ∀ i : I, (M i).MullerAccept (accSet i) as := by sorry
