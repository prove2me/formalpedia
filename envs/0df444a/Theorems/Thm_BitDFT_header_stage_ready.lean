-- Prove2me | Theorems.Thm_BitDFT_header_stage_ready
-- name    : BitDFT.header_stage_ready
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:31:16.786793+00:00
-- url     : https://prove2.me/theorems/ac6acb94-e476-407e-8af2-c6a4e48e6785
-- title:
--   A composable header stage halts after exactly 2k+3 transitions
-- statement:
--   For binary words v and r with k=|v|, the finite header stage on input 1^k 0 v r has halted after 2k+3 transitions. Its input head points to the start of r; its field tape contains exactly v and its head is at k+1. Its counter tape is empty beyond its start marker with head at zero. Its native output is still empty with head at one. These exact tape and head guarantees supply the handoff configuration for the next wrapper stage, independently of the length of r.
-- source:
--   Strengthens the already proved header_reader_ready result by making the internal boundary a real frozen exit. Direct phase invariants show that the original reader never reaches the boundary earlier, so the stopping adapter preserves the exact run. This is one wrapper component, not a proof of the full rescaling machine.

import Definitions.Def_BitDFT_HeaderStage
open BitDFT BitDFT.HeaderReader IntMul

theorem BitDFT.header_stage_ready (v rest : List Bool) :
    let x := List.replicate v.length true ++ false :: (v ++ rest)
    let c := stage.machine.step^[2*v.length+3] (stage.machine.initCfg x [])
    c.state = stage.exit ∧ c.head 0 = 2*v.length+2 ∧
    c.cells 3 = stage.machine.tapeOf (v.map stage.machine.bitSym) ∧
    c.cells 2 = stage.machine.tapeOf [] ∧ c.head 2 = 0 ∧
    c.cells 1 = stage.machine.tapeOf [] ∧ c.head 1 = 1 ∧ c.head 3 = v.length+1 := by sorry
