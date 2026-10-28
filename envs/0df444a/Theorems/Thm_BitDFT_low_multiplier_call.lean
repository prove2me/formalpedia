-- Prove2me | Theorems.Thm_BitDFT_low_multiplier_call
-- name    : BitDFT.low_multiplier_call
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T19:11:32.622032+00:00
-- url     : https://prove2.me/theorems/7b776fab-db2d-4599-9bf3-ccd283d38feb
-- title:
--   Call the arbitrary multiplier at width q on the low magnitude
-- statement:
--   Let the supplied machine multiply all q-bit inputs within T steps. For q≥1, n<2^q, and a≤2^q, its clean wrapper executes on the q-bit encodings of n and a mod 2^q, returns the exact q-bit by q-bit product in 36T steps, and satisfies the exact high-bit selection identity for na. In particular the multiplier is called only at width q, including when a=2^q.
-- source:
--   Actual arbitrary-multiplier invocation for the finite-precision DFT output scaler.

import Theorems.Thm_BitDFT_clean_multiplier_call
import Theorems.Thm_BitDFT_scalar_low_product_selection
open IntMul

theorem BitDFT.low_multiplier_call (M : MultitapeTM) (q n a : ℕ) (T : ℝ)
    (hq : 1 ≤ q) (hn : n < 2^q) (ha : a ≤ 2^q) (hM : MultipliesAt M q T) :
    ∃ t : ℕ,
      (t : ℝ) ≤ 36*T ∧
      (IntMul.TrackedNativeCall.machine M).HaltsWithOutput
        (bin q n) (bin q (a%2^q)) t (bin (2*q) (n*(a%2^q))) ∧
      n*a = (if a.testBit q then n*2^q else n*(a%2^q)) := by sorry
