-- Prove2me | Theorems.Thm_Automata_da_concat_ptr2_antitone
-- name    : Automata.da_concat_ptr2_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:33:28.476519+00:00
-- url     : https://prove2.me/theorems/331ed3c7-4adc-49ad-8847-9fa08d1cc62b
-- title:
--   Automata: da concat ptr2 antitone
-- statement:
--   The value of `DA.ConcatPtr2` is a non-increasing over time.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/DetConcat.lean#L207-L216
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/DetConcat.lean#L207-L216

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

theorem Automata.da_concat_ptr2_antitone (as : Stream' A) (n : ℕ) (h_n : M1.DetRun as n ∈ acc1):
    Antitone (DA.ConcatPtr2 M1 acc1 M2 as n h_n) := by sorry
