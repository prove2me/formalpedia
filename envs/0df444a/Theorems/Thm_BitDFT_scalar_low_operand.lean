-- Prove2me | Theorems.Thm_BitDFT_scalar_low_operand
-- name    : BitDFT.scalar_low_operand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T19:06:17.476605+00:00
-- url     : https://prove2.me/theorems/c361c3e5-8ee3-4ffa-a544-d7f438b80ee9
-- title:
--   Skipping sign and high bit gives exactly the q-bit low-magnitude operand
-- statement:
--   For any integer z and natural q, removing the sign and leading magnitude bit from the fixed-width signed encoding with q+1 magnitude bits gives exactly the q-bit encoding of |z| mod 2^q. The remaining word has length q and represents an integer strictly below 2^q. This identifies the operand obtained by copying the remaining scratch word into a q-bit multiplier input.
-- source:
--   Exact coordinate scaling for the integer multiplication to finite-precision DFT mission.

import Definitions.Def_BitDFT_Encoding
open BitDFT IntMul

theorem BitDFT.scalar_low_operand (q : ℕ) (z : ℤ) :
    (encInt (q+1) z).drop 2 = bin q (z.natAbs % 2^q) ∧
    ((encInt (q+1) z).drop 2).length = q ∧
    z.natAbs % 2^q < 2^q := by sorry
