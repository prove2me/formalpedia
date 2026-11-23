-- Prove2me | Theorems.Thm_Automata_da_concat_to_muller_accept
-- name    : Automata.da_concat_to_muller_accept
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:33:37.666516+00:00
-- url     : https://prove2.me/theorems/07a42731-566b-4a17-bf57-b241400e8b32
-- title:
--   Automata: da concat to muller accept
-- statement:
--   Any infinite word consisting of a finite word accepted by `M1` followed by
--   an infinite word accepted by `M2` under the Muller condition is accepted by
--   `M1.Concat acc1 M2` under the Muller condition
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/DetConcat.lean#L243-L271
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/DetConcat.lean#L243-L271

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

theorem Automata.da_concat_to_muller_accept (as : Stream' A) (n : ℕ)
    (h1 : M1.toNA.FinAccept acc1 n as) (h2 : M2.MullerAccept accSet2 (as.drop n)) :
    (M1.Concat acc1 M2).MullerAccept (DA.MullerAcc_Concat M1 acc1 M2 accSet2) as := by sorry
