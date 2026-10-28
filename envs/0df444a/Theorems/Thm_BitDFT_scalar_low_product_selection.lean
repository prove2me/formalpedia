-- Prove2me | Theorems.Thm_BitDFT_scalar_low_product_selection
-- name    : BitDFT.scalar_low_product_selection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T19:06:02.529018+00:00
-- url     : https://prove2.me/theorems/c95f4185-39bf-40f7-b9c8-ca6c1c6397aa
-- title:
--   One q-bit multiplication suffices before selecting the scaled magnitude
-- statement:
--   For nonnegative a≤2^q and n, the residue a mod 2^q fits in q bits. The exact product na equals n times that residue when the high bit is zero, and n2^q when it is one. In the latter case the residue and its product are zero. Thus a scaler can always make the same q-bit multiplication call, then select its output or a shifted copy of n during serialization; it needs no call at width q+1.
-- source:
--   Exact coordinate scaling for the integer multiplication to finite-precision DFT mission.

import Definitions.Def_BitDFT_Numerics
open BitDFT IntMul

theorem BitDFT.scalar_low_product_selection (q a n : ℕ) (ha : a ≤ 2^q) :
    a % 2^q < 2^q ∧
    n*a = (if a.testBit q then n*2^q else n*(a % 2^q)) ∧
    (a.testBit q = true → a % 2^q = 0 ∧ n*(a % 2^q) = 0) := by sorry
