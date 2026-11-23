-- Prove2me | Theorems.Thm_Automata_da_concat_ptr2_eventually
-- name    : Automata.da_concat_ptr2_eventually
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:33:34.799797+00:00
-- url     : https://prove2.me/theorems/6f9bd362-d10e-4a9f-92fa-91d9c0f7b322
-- title:
--   Automata: da concat ptr2 eventually
-- statement:
--   Thus `DA.ConcatPtr2` must stabilize at some value `i` from some time `m` onward.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/DetConcat.lean#L220-L224
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/DetConcat.lean#L220-L224

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

theorem Automata.da_concat_ptr2_eventually (as : Stream' A) (n : ℕ) (h_n : M1.DetRun as n ∈ acc1):
    ∃ i : Fin (Nat.card M2.State + 2), ∃ m > n, ∀ k ≥ m, DA.ConcatPtr2 M1 acc1 M2 as n h_n (k - n - 1) = i := by sorry
