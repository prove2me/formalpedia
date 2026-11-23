-- Prove2me | Theorems.Thm_Automata_da_concat_of_muller_accept
-- name    : Automata.da_concat_of_muller_accept
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:33:36.417809+00:00
-- url     : https://prove2.me/theorems/e7ec8e25-124e-4342-b2fb-acf56479ae19
-- title:
--   Automata: da concat of muller accept
-- statement:
--   Any infinite word accepted by `M1.Concat acc1 M2` under the Muller condition
--   consists of a finite word accepted by `M1` followed by an infinite word accepted
--   by `M2` under the Muller condition.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/DetConcat.lean#L277-L300
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/DetConcat.lean#L277-L300

import Definitions.Def_AutomataTheory_Automata_Det
import Definitions.Def_AutomataTheory_Automata_DetConcat
set_option autoImplicit true
open Function Set Prod Option Filter Stream'
open Classical
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type} (M1 : DA A) (acc1 : Set M1.State) (M2 : DA A)
attribute [local instance_reducible] DA.Concat
variable [Finite M2.State]
variable [Finite M1.State]
variable (accSet2 : Set (Set M2.State))

theorem Automata.da_concat_of_muller_accept (as : Stream' A)
    (h : (M1.Concat acc1 M2).MullerAccept (DA.MullerAcc_Concat M1 acc1 M2 accSet2) as) :
    ∃ n, M1.toNA.FinAccept acc1 n as ∧ M2.MullerAccept accSet2 (as.drop n) := by sorry
