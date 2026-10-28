-- Prove2me | Theorems.Thm_BitDFT_extraction_ready
-- name    : BitDFT.extraction_ready
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T18:53:12.802629+00:00
-- url     : https://prove2.me/theorems/acf2e3aa-7b69-4a5f-a109-5490966cfad6
-- title:
--   Fresh scratch preparation adds at most two steps to vector initialization
-- statement:
--   If the vector-initialization machine halts after t transitions on inputs x and y, the extended machine reaches the specified full extraction-ready configuration within t+2 transitions. The added scratch tape is blank with its head at the first data cell. All prior tapes and heads are preserved. Tape extension and index identification exactly preserve execution; the controller handoff and scratch-head movement each cost one step.
-- source:
--   Actual-machine initialization for the exact Fourier output scaler. Coordinate multiplication and serialization remain separate obligations.

import Definitions.Def_BitDFT_ExtractionReady
open BitDFT.ExtractionReady BitDFT IntMul MachineSequence

theorem BitDFT.extraction_ready (M : MultitapeTM) (x y : List Bool) (t : ℕ)
    (halt : ((VectorReady.machine M).step^[t] ((VectorReady.machine M).initCfg x y)).state =
      (VectorReady.machine M).qHalt) :
    ∃ u : ℕ, u ≤ t+2 ∧
      (machine M).step^[u] ((machine M).initCfg x y) =
        final M ((VectorReady.machine M).step^[t] ((VectorReady.machine M).initCfg x y)) := by sorry
