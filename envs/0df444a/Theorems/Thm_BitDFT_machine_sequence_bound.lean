-- Prove2me | Theorems.Thm_BitDFT_machine_sequence_bound
-- name    : BitDFT.machine_sequence_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:22:52.76416+00:00
-- url     : https://prove2.me/theorems/4883f155-228c-454f-a372-2cfe442c651e
-- title:
--   Sequential machine execution adds at most one handoff transition
-- statement:
--   For two finite controllers sharing the same tape alphabet and layout, if the first controller has halted by time t, the composed machine reaches exactly the second controller configuration obtained after u additional steps, within t+1+u transitions. The second controller inherits every tape cell and head position. The first runtime may be an upper bound rather than the first halting time. The conclusion is an equality of full machine configurations.
-- source:
--   Direct proof from the finite transition table of BitDFT_MachineSequence. The proof selects the least halting time, proves that all later first-controller configurations are frozen, and composes the exact runs. This is a composition component; it does not by itself construct the Fourier or rescaling algorithms.

import Definitions.Def_BitDFT_MachineSequence
open BitDFT.MachineSequence IntMul

theorem BitDFT.machine_sequence_bound {M : MultitapeTM} (P Q : Controller M) (c : P.machine.Cfg)
    (t u : ℕ) (ht : (P.machine.step^[t] c).state = P.exit) :
    ∃ v ≤ t + 1 + u,
      (sequence P Q).machine.step^[v] (leftCfg P Q c) =
        rightCfg P Q (Q.machine.step^[u] (handoff P Q (P.machine.step^[t] c))) := by sorry
