-- Prove2me | Theorems.Thm_BitDFT_header_reader_ready
-- name    : BitDFT.header_reader_ready
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T13:59:14.671671+00:00
-- url     : https://prove2.me/theorems/cf195e45-6315-41e5-ae84-fa654fa5e1c9
-- title:
--   A binary field is parsed in 2k+3 transitions before scanning the remaining input
-- statement:
--   For arbitrary binary words $v,r$, let $k=|v|$. After exactly $2k+3$ transitions on input $1^k0vr$, the fixed header reader is at its copying-state boundary. The input head points to the first bit of $r$ (or the separator if $r$ is empty); the field tape contains exactly $v$; the counter tape and native output tape are blank beyond their permanent markers. Their heads are respectively at positions $0$ and $1$, and the field head is at $k+1$.
--
--   This is a configuration-level handoff guarantee. Its cost is independent of the length of $r$, so a surrounding wrapper can continue without first copying a long vector. The copying state is not a halting state.
-- source:
--   Original prefix-and-field phase invariant for Definitions.Def_BitDFT_HeaderReader. Complements the proved complete-run theorem BitDFT.header_reader_correct, https://prove2.me/theorems/c527fd43-000a-4663-afc8-f8a5c254188c. It uses the actual step function and the finite reader transition table, not an abstract parsing oracle.

import Definitions.Def_BitDFT_HeaderReader
open BitDFT.HeaderReader

theorem BitDFT.header_reader_ready (v rest : List Bool) :
    let x := List.replicate v.length true ++ false :: (v ++ rest)
    let c := machine.step^[2 * v.length + 3] (machine.initCfg x [])
    c.state = State.copy ∧ c.head 0 = 2 * v.length + 2 ∧
      c.cells 3 = machine.tapeOf (v.map machine.bitSym) ∧
      c.cells 2 = machine.tapeOf [] ∧ c.head 2 = 0 ∧
      c.cells 1 = machine.tapeOf [] ∧ c.head 1 = 1 ∧ c.head 3 = v.length+1 := by sorry
