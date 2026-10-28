-- Prove2me | Theorems.Thm_BitDFT_coordinate_scalar_call
-- name    : BitDFT.coordinate_scalar_call
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T08:46:10.879478+00:00
-- url     : https://prove2.me/theorems/b8de222b-7d83-4eb4-8b49-d4e4dc8198aa
-- title:
--   Multiply a signed Fourier coordinate at the supplied q-bit width
-- statement:
--   Let a signed integer coordinate z have magnitude at most 2^q, and let n<2^q. If the supplied machine multiplies q-bit operands within T steps, then a clean q-bit multiplication call computes n times the low-q-bit residue of |z| in at most 36T steps. The high bit selects the exact boundary product when |z|=2^q, and the signed result fits q+lg(n)+1 magnitude bits with the same sign as z when n is positive.
-- source:
--   The scalar arithmetic and machine-call interface for the integer-multiplication to finite-precision Fourier transfer mission.

import Theorems.Thm_BitDFT_clean_multiplier_call
import Theorems.Thm_BitDFT_scalar_low_product_selection
import Theorems.Thm_BitDFT_scalar_product_width
import Definitions.Def_BitDFT_Encoding
import Mathlib.Tactic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.OfFn
set_option autoImplicit false
open IntMul

theorem BitDFT.coordinate_scalar_call (M : MultitapeTM) (q n : ℕ) (T : ℝ) (z : ℤ)
    (hq : 1 ≤ q) (hn : n < 2^q) (hz : z.natAbs ≤ 2^q)
    (hM : MultipliesAt M q T) :
    ∃ t : ℕ,
      (t : ℝ) ≤ 36*T ∧
      (IntMul.TrackedNativeCall.machine M).HaltsWithOutput
        (bin q n) (bin q (z.natAbs % 2^q)) t
        (bin (2*q) (n*(z.natAbs % 2^q))) ∧
      n*z.natAbs = (if z.natAbs.testBit q then n*2^q
        else n*(z.natAbs % 2^q)) ∧
      ((n : ℤ)*z).natAbs < 2^(q+lg n+1) ∧
      (0 < n → (((n : ℤ)*z < 0) ↔ z < 0)) := by sorry
