-- Prove2me | Theorems.Thm_BitDFT_counted_block_correct
-- name    : BitDFT.counted_block_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T17:51:38.462785+00:00
-- url     : https://prove2.me/theorems/bab7d0dd-3759-4c3b-a2e1-2ef4b665480d
-- title:
--   Copy a counted block and reset its descriptor in linear time independent of surrounding data
-- statement:
--   Let y be a binary descriptor and B=val(y)+1. From the specified live frame, with at least B payload bits remaining, the fixed machine copies the next B bits after any existing output prefix and halts within 6B+4|y|+2 transitions. Both descriptor tapes are restored, their heads return to the low-order end, and the input/output heads advance by exactly B. The bound is independent of the surrounding input and existing output lengths. Leading-zero and empty descriptors are allowed. Preparation of the starting frame is a separate charged task.
-- source:
--   Reuses and adapts the accepted counted-stream proof, submission e6e59750-1549-470d-a25a-2b51eb6f6a99: https://prove2.me/submissions/e6e59750-1549-470d-a25a-2b51eb6f6a99 . Generalized for scalar-coordinate extraction without a whole-vector scan per coordinate.

import Definitions.Def_BitDFT_CountedBlock
open IntMul IntMul.CountedStream
open IntMul.TapeCopy (Sym)

theorem BitDFT.counted_block_correct (pre out x y : List Bool) (hx : IntMul.val y+1 ≤ x.length) :
    ∃ t : ℕ, t ≤ 6*(IntMul.val y+1)+4*y.length+2 ∧
      machine.step^[t] (BitDFT.CountedBlock.frame pre out x y y.reverse 0 .emit) =
        BitDFT.CountedBlock.frame pre out x y y.reverse (IntMul.val y+1) .halt := by sorry
