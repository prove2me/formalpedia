-- Prove2me | Theorems.Thm_BitDFT_low_operand_call_input
-- name    : BitDFT.low_operand_call_input
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T00:19:09.9735+00:00
-- url     : https://prove2.me/theorems/fb6964d3-a88b-4b13-8dbc-41db2a0ffedc
-- title:
--   Copied low bits form the clean multiplier operand
-- statement:
--   For an integer z and precision q, its signed encoding at q+1 magnitude bits splits into the sign bit, the magnitude bit at position q, and the q low-order bits. The fixed low-operand copier preserves the source and writes exactly those low bits to the clean multiplier-input tape, halting within q+5 transitions. This identifies the copier's physical tape output with the binary encoding of |z| modulo 2^q, including the boundary case where the high bit is set.
-- source:
--   Exact encoding-to-tape interface for the low-operand copier used by output rescaling.

import Definitions.Def_BitDFT_LowOperandCopy
import Definitions.Def_BitDFT_Encoding
import Theorems.Thm_BitDFT_low_operand_copy_correct
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bitwise
set_option autoImplicit false
open BitDFT BitDFT.LowOperandCopy IntMul

theorem BitDFT.low_operand_call_input (q : ℕ) (z : ℤ) :
    encInt (q+1) z = decide (z < 0) :: (z.natAbs).testBit q ::
      bin q (z.natAbs % 2^q) ∧
    (∃ t : ℕ, t ≤ q+5 ∧
      (machine (show sourceTape ≠ counterTape from by decide)).step^[t]
        (initial (show sourceTape ≠ counterTape from by decide)
          (decide (z < 0)) ((z.natAbs).testBit q) (bin q (z.natAbs % 2^q))) =
        final (show sourceTape ≠ counterTape from by decide)
          (decide (z < 0)) ((z.natAbs).testBit q) (bin q (z.natAbs % 2^q))) ∧
    (final (show sourceTape ≠ counterTape from by decide)
      (decide (z < 0)) ((z.natAbs).testBit q) (bin q (z.natAbs % 2^q))).cells
        ⟨1, by simp [storage]⟩ =
      storage.tapeOf ((bin q (z.natAbs % 2^q)).map storage.bitSym) := by sorry
