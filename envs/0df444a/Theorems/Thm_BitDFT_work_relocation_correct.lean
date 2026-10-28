-- Prove2me | Theorems.Thm_BitDFT_work_relocation_correct
-- name    : BitDFT.work_relocation_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T17:56:29.685985+00:00
-- url     : https://prove2.me/theorems/be8f6663-5d83-4bd9-98fd-1c1dbfa3ff4a
-- title:
--   Work-tape relocation preserves every transition and the original input
-- statement:
--   For every machine M, arbitrary parked input contents and head position, starting configuration c, and time t, the relocated machine reaches exactly the embedding of the configuration reached by M after t transitions. Throughout this run the new native input tape and its head are unchanged. This is an exact clock-preserving simulation from the stated full configuration; preparation of that configuration is separate.
-- source:
--   Machine adapter used to extract coordinate records from a previously computed Fourier output.

import Definitions.Def_BitDFT_WorkRelocation
open BitDFT.WorkRelocation IntMul

theorem BitDFT.work_relocation_correct (M : MultitapeTM) (rootCells : ℕ → M.Sym) (rootHead : ℕ) (c : M.Cfg) (t : ℕ) :
    (machine M).step^[t] (embed M rootCells rootHead c) = embed M rootCells rootHead (M.step^[t] c) ∧
      ((machine M).step^[t] (embed M rootCells rootHead c)).cells (machine M).inTape = rootCells ∧
      ((machine M).step^[t] (embed M rootCells rootHead c)).head (machine M).inTape = rootHead := by sorry
