-- Prove2me | Theorems.Thm_BitDFT_counted_block_correct_on_work_tapes
-- name    : BitDFT.counted_block_correct_on_work_tapes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T04:41:45.120853+00:00
-- url     : https://prove2.me/theorems/0514ac0e-445f-4283-af1d-6e75acccc933
-- title:
--   Counted-block serialization on work tapes preserves the caller
-- statement:
--   Let a source block x be long enough for a binary descriptor y to count out val(y)+1 bits. The counted-block serializer can run on work tapes 1 through 4 while the machine's input tape 0 and the caller's other data remain unchanged. It reaches the corresponding completed frame within 6(val(y)+1)+4|y|+2 transitions.
-- source:
--   The proof reuses the accepted counted-block run and proves an exact step-by-step simulation after relocating its four logical tapes to work tapes 1–4.

import Definitions.Def_BitDFT_CountedBlockOnWorkTapes
import Theorems.Thm_BitDFT_counted_block_correct
set_option autoImplicit false
open IntMul

theorem BitDFT.counted_block_correct_on_work_tapes
    (base : BitDFT.CountedBlockOnWorkTapes.machine.Cfg)
    (pre out x y : List Bool) (hx : val y + 1 ≤ x.length) :
    ∃ t : ℕ, t ≤ 6*(val y+1)+4*y.length+2 ∧
      BitDFT.CountedBlockOnWorkTapes.machine.step^[t]
        (BitDFT.CountedBlockOnWorkTapes.embed base
          (BitDFT.CountedBlock.frame pre out x y y.reverse 0 .emit)) =
      BitDFT.CountedBlockOnWorkTapes.embed base
        (BitDFT.CountedBlock.frame pre out x y y.reverse (val y+1) .halt) := by sorry
