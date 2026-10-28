-- Prove2me | Theorems.Thm_BitDFT_work_signed_block_correct
-- name    : BitDFT.work_signed_block_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T18:47:41.716387+00:00
-- url     : https://prove2.me/theorems/7812d281-35a5-4f6c-82fa-f40755128f96
-- title:
--   Extract a signed coordinate from a work tape with the native input parked
-- statement:
--   Given the specified initialized descriptor tapes and at least B=val(y)+1 magnitude bits, copy the current sign and next B magnitude bits from work tape 1 to work tape 2 within 6B+4|y|+4 transitions. Both descriptor tapes are restored and both data heads advance by B+1. The complete final configuration preserves the arbitrary native input and its head. The bound excludes preparation of the explicit starting frame.
-- source:
--   Composition of exact work-tape relocation with the counted-block extraction theorem for Fourier coordinate scaling.

import Definitions.Def_BitDFT_WorkRelocation
import Definitions.Def_BitDFT_SignedBlock
open IntMul BitDFT.SignedBlock

theorem BitDFT.work_signed_block_correct (rootCells : ℕ → TapeCopy.Sym) (rootHead : ℕ)
    (pre out : List Bool) (sign : Bool) (x y : List Bool) (hx : val y+1 ≤ x.length) :
    ∃ t : ℕ, t ≤ 6*(val y+1)+4*y.length+4 ∧
      (BitDFT.WorkRelocation.machine machine).step^[t]
        (BitDFT.WorkRelocation.embed machine rootCells rootHead (initial pre out sign x y)) =
      BitDFT.WorkRelocation.embed machine rootCells rootHead (final pre out sign x y) := by sorry
