-- Prove2me | Theorems.Thm_BitDFT_signed_block_correct
-- name    : BitDFT.signed_block_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T18:47:10.180881+00:00
-- url     : https://prove2.me/theorems/ae4f071d-77ad-443d-9522-7b3fc4e4865b
-- title:
--   Extract a sign and counted magnitude with restored descriptors and a linear clock
-- statement:
--   Let B=val(y)+1, and suppose at least B payload bits remain after the current sign bit. From the specified full starting configuration, the signed-record extractor appends the sign and the next B payload bits to its output and reaches its specified final configuration within 6B+4|y|+4 transitions. Both descriptor tapes are restored, both data heads advance by B+1, and the input remains unchanged. The bound is independent of the preceding input and output lengths. Descriptor initialization and routing into this starting frame are separate charged obligations.
-- source:
--   Signed-coordinate extraction for the exact Fourier output scaler.

import Definitions.Def_BitDFT_SignedBlock
open BitDFT.SignedBlock BitDFT IntMul MachineSequence

theorem BitDFT.signed_block_correct (pre out : List Bool) (sign : Bool) (x y : List Bool) (hx : val y+1 ≤ x.length) :
    ∃ t : ℕ, t ≤ 6*(val y+1)+4*y.length+4 ∧
      machine.step^[t] (initial pre out sign x y) = final pre out sign x y := by sorry
