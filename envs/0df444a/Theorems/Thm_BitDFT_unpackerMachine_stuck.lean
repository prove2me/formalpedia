-- Prove2me | Theorems.Thm_BitDFT_unpackerMachine_stuck
-- name    : BitDFT.unpackerMachine_stuck
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T05:30:24.785413+00:00
-- url     : https://prove2.me/theorems/634f0614-69bf-4458-983e-d8e5ff610b76
-- title:
--   The first unpacking machine cannot leave its initial cell
-- statement:
--   A machine in this multitape model must keep the end marker $\triangleright$ in place on any tape whose head scans it, and must never move a head left off it. The guard of `BitDFT_unpackerMachine` enforces this by turning *every* move on such a cell into a stay.
--
--   The initial configuration has every head on cell $0$, which holds the end marker on every tape. Consequently the guard overrides the intended first transition — which is to step the input head right onto the first symbol of the encoding — and the input head is still on cell $0$ after one step. No phase that requires leaving the marker can ever advance, so the machine computes nothing.
--
--   This is the reason the definition was superseded by `BitDFT_unpackerMachineV2`, whose guard keeps the written symbol and replaces only a *leftward* move by a stay, allowing a rightward move away from the marker as the model permits.
-- source:
--   Internal: defect report for BitDFT_unpackerMachine, found while proving the first transition lemma for Prove2me's BitDFT.unpacking_machine (https://prove2.me/theorems/3a9d0791-96d8-4079-919b-de51b895da98). Corrected in BitDFT_unpackerMachineV2.

import Definitions.Def_BitDFT_unpackerMachine

theorem BitDFT.unpackerMachine_stuck (x y : List Bool) :
    (BitDFT.Unpacker.machine.step (BitDFT.Unpacker.machine.initCfg x y)).head
      BitDFT.Unpacker.machine.inTape = 0 := by sorry
