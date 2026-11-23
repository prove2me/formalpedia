-- Prove2me | Theorems.Thm_Automata_da_concat_det_run_2
-- name    : Automata.da_concat_det_run_2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:33:25.085459+00:00
-- url     : https://prove2.me/theorems/34b4c94b-a551-4de1-8d41-47e4d73aefe4
-- title:
--   Automata: da concat det run 2
-- statement:
--   If any `M2` copy in the second state component of `M1.Concat acc1 M2` ever
--   stabilizes (in the sense of never being deactivated from some point on), then
--   it contains an infinite run of `M2` starting from its activation.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/DetConcat.lean#L80-L122
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/DetConcat.lean#L80-L122

import Definitions.Def_AutomataTheory_Automata_Det
import Definitions.Def_AutomataTheory_Automata_DetConcat
set_option autoImplicit true
open Function Set Prod Option Filter Stream'
open Classical
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type} (M1 : DA A) (acc1 : Set M1.State) (M2 : DA A)
attribute [local instance_reducible] DA.Concat

theorem Automata.da_concat_det_run_2 (as : Stream' A) (n : ℕ) (i : Fin (Nat.card M2.State + 2))
    (h : ∀ k ≥ n, (((M1.Concat acc1 M2).DetRun as k).2 i).isSome) :
    ∃ m < n, M1.DetRun as m ∈ acc1 ∧
      ∀ k > m, ((M1.Concat acc1 M2).DetRun as k).2 i = some (M2.DetRun (as.drop m) (k - m)) := by sorry
