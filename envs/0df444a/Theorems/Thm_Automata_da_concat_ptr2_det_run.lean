-- Prove2me | Theorems.Thm_Automata_da_concat_ptr2_det_run
-- name    : Automata.da_concat_ptr2_det_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:33:25.292497+00:00
-- url     : https://prove2.me/theorems/6a3258e7-f8b2-4be8-b12d-e1b363359388
-- title:
--   Automata: da concat ptr2 det run
-- statement:
--   `DA.ConcatPtr2` always point to an active `M2` copy whose state is consistent with
--   its being activated at step `n`.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/DetConcat.lean#L200-L203
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/DetConcat.lean#L200-L203

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

theorem Automata.da_concat_ptr2_det_run (as : Stream' A) (n : ℕ) (h_n : M1.DetRun as n ∈ acc1) (k : ℕ) :
    ((M1.Concat acc1 M2).DetRun as (n + k + 1)).2 (DA.ConcatPtr2 M1 acc1 M2 as n h_n k) =
    some (M2.DetRun (as.drop n) (k + 1)) := by sorry
