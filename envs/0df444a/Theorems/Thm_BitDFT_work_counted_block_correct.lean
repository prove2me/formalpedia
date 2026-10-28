-- Prove2me | Theorems.Thm_BitDFT_work_counted_block_correct
-- name    : BitDFT.work_counted_block_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T17:56:56.249419+00:00
-- url     : https://prove2.me/theorems/156666d6-af16-4725-bef0-452b98459079
-- title:
--   Extract a counted payload block from a work tape without moving the native input
-- statement:
--   Let y be a binary descriptor and B=val(y)+1. Given at least B unread payload bits and the specified initialized counter and template tapes, the relocated counted-block machine copies the next B bits from work tape 1 to work tape 2 in at most 6B+4|y|+2 transitions. The native input is parked with arbitrary contents and head position. The complete ending configuration includes the copied payload, advanced work-tape heads, restored descriptor tapes, and the unchanged native input. Preparation of this starting configuration is not included in the bound.
-- source:
--   Composition of exact work-tape relocation with the counted-block extraction theorem for Fourier coordinate scaling.

import Definitions.Def_BitDFT_WorkRelocation
import Definitions.Def_BitDFT_CountedBlock
open IntMul

theorem BitDFT.work_counted_block_correct (rootCells : ℕ → TapeCopy.Sym) (rootHead : ℕ)
    (pre out x y : List Bool) (hx : val y+1 ≤ x.length) :
    ∃ t : ℕ, t ≤ 6*(val y+1)+4*y.length+2 ∧
      (BitDFT.WorkRelocation.machine CountedStream.machine).step^[t]
        (BitDFT.WorkRelocation.embed CountedStream.machine rootCells rootHead
          (BitDFT.CountedBlock.frame pre out x y y.reverse 0 .emit)) =
      BitDFT.WorkRelocation.embed CountedStream.machine rootCells rootHead
          (BitDFT.CountedBlock.frame pre out x y y.reverse (val y+1) .halt) := by sorry
