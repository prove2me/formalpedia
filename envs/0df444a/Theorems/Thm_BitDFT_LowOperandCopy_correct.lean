-- Prove2me | Theorems.Thm_BitDFT_LowOperandCopy_correct
-- name    : BitDFT.LowOperandCopy.correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T23:54:15.251986+00:00
-- url     : https://prove2.me/theorems/c96db71e-7948-470c-a568-935705ed31ff
-- title:
--   Extract the low operand bits in linear time
-- statement:
--   Let a signed binary word consist of a sign bit, a highest magnitude bit, and a suffix of q low-order bits. A three-tape machine preserves the input word, skips the first two bits using a unary counter, copies exactly the q-bit suffix to a clean operand tape, and halts with the source head at the delimiter and the output head just past the copied word. Its running time is at most q+5 transitions.
-- source:
--   Composes unary-controlled head positioning with the two-tape suffix copier to supply the low operand used by the scaled multiplication simulation.

import Definitions.Def_BitDFT_LowOperandCopy
import Definitions.Def_BitDFT_UnaryAdvance
import Definitions.Def_BitDFT_MachineSequence
import Definitions.Def_BitDFT_SuffixCopyTwoTape
open IntMul BitDFT.MachineSequence

theorem BitDFT.LowOperandCopy.correct (h : sourceTape ≠ counterTape) (sign high : Bool) (bits : List Bool) :
    ∃ t : ℕ, t ≤ bits.length + 5 ∧
      (machine h).step^[t] (initial h sign high bits) = final h sign high bits := by sorry
