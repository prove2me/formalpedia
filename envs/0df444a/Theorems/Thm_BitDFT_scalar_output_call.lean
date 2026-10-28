-- Prove2me | Theorems.Thm_BitDFT_scalar_output_call
-- name    : BitDFT.scalar_output_call
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T00:33:00.747031+00:00
-- url     : https://prove2.me/theorems/5b1b6cf7-71e0-4556-9205-d55f19ef5772
-- title:
--   A signed coordinate's copied low word feeds its exact scaling call
-- statement:
--   For a signed integer coordinate z and precision q, its signed encoding separates into its sign, its q-th magnitude bit, and the q lower magnitude bits. The fixed copier writes those lower bits to the multiplier-input tape in at most q+5 transitions. A clean call to any supplied q-bit multiplier on n and that same low-bit word returns the exact 2q-bit product within 36T steps. Selecting according to the high bit recovers n times the full magnitude, with the correctly padded output-width encoding. The claim includes the boundary magnitude 2^q.
-- source:
--   Composition interface between the proved signed low-bit copier and the proved q-bit multiplier-backed scalar scaler.

import Theorems.Thm_BitDFT_low_operand_call_input
import Theorems.Thm_BitDFT_scaled_call_word
import Definitions.Def_BitDFT_Encoding
set_option autoImplicit false
open BitDFT BitDFT.LowOperandCopy IntMul

theorem BitDFT.scalar_output_call (M : MultitapeTM) (q n : ℕ) (z : ℤ) (T : ℝ)
    (hq : 1 ≤ q) (hnq : n < 2^q)
    (hqwide : lg n + 1 ≤ q) (hnwide : n ≤ 2^(lg n))
    (hz : z.natAbs ≤ 2^q) (hM : MultipliesAt M q T) :
    let h : sourceTape ≠ counterTape := (show sourceTape ≠ counterTape from by decide)
    let sign := decide (z < 0)
    let mag := z.natAbs
    let high := mag.testBit q
    let bits := bin q (mag % 2^q)
    encInt (q+1) z = sign :: high :: bits ∧
    (∃ tc : ℕ, tc ≤ q+5 ∧
      (machine h).step^[tc] (initial h sign high bits) = final h sign high bits) ∧
    (final h sign high bits).cells ⟨1, by simp [storage]⟩ =
      storage.tapeOf (bits.map storage.bitSym) ∧
    (∃ tm : ℕ, (tm : ℝ) ≤ 36*T ∧
      (IntMul.TrackedNativeCall.machine M).HaltsWithOutput
        (bin q n) (bin q (mag % 2^q)) tm (bin (2*q) (n*(mag % 2^q)))) ∧
    (if high then n*2^q else n*(mag % 2^q)) = n*mag ∧
    bin (2*q) (if high then n*2^q else n*(mag % 2^q)) =
      List.replicate (2*q-(q+lg n+1)) false ++
        bin (q+lg n+1) (if high then n*2^q else n*(mag % 2^q)) := by sorry
