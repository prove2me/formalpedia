-- Prove2me | Theorems.Thm_BitDFT_low_operand_copy_correct
-- name    : BitDFT.low_operand_copy_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T00:11:18.539986+00:00
-- url     : https://prove2.me/theorems/4bdf0ec8-a4ff-4fba-ba59-da9572d94f5a
-- title:
--   Extract a signed word's low operand bits
-- statement:
--   A fixed three-tape machine preserves a signed binary source word, skips its sign and highest magnitude bit with a unary counter, copies the remaining q low-order bits to a clean operand tape, and halts in the specified source, output, and counter positions within q+5 transitions.
-- source:
--   Importable interface for the proved low-operand extraction stage used by the scalar multiplication subroutine in output rescaling.

import Definitions.Def_BitDFT_LowOperandCopy
open IntMul BitDFT.LowOperandCopy BitDFT.MachineSequence

theorem BitDFT.low_operand_copy_correct (h : sourceTape ≠ counterTape) (sign high : Bool) (bits : List Bool) :
    ∃ t : ℕ, t ≤ bits.length + 5 ∧
      (machine h).step^[t] (initial h sign high bits) = final h sign high bits := by sorry
