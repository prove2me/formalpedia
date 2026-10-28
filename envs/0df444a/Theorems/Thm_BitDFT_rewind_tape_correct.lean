-- Prove2me | Theorems.Thm_BitDFT_rewind_tape_correct
-- name    : BitDFT.rewind_tape_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T18:09:56.979996+00:00
-- url     : https://prove2.me/theorems/9d32310e-6cce-4b21-aa9c-0ef0f9d11e09
-- title:
--   Rewind one selected tape to its first data cell with an exact clock
-- statement:
--   For an arbitrary finite multitape machine alphabet and a selected tape, assume the tape has its start marker exactly at position zero. From head position p, the rewind controller halts at position one in exactly p+1 transitions. All tape contents and all other heads are preserved. The initial head position is part of the full specified configuration.
-- source:
--   Charged setup for the exact output scaler in the finite-precision DFT transfer mission.

import Definitions.Def_BitDFT_RewindTape
open BitDFT IntMul
open BitDFT.RewindTape

theorem BitDFT.rewind_tape_correct (N : MultitapeTM) (j : Fin N.k) (base : N.Cfg)
    (hz : base.cells j 0 = N.startSym)
    (hn : ∀ p, 0 < p → base.cells j p ≠ N.startSym) (p : ℕ) :
    (machine N j).step^[p+1] (frame N j base false p) = frame N j base true 1 := by sorry
