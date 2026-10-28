-- Prove2me | Theorems.Thm_BitDFT_scalar_product_width
-- name    : BitDFT.scalar_product_width
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T17:59:30.209446+00:00
-- url     : https://prove2.me/theorems/1f9cf551-7f16-423e-af96-e11c1c11f08c
-- title:
--   Exact coordinate scaling fits the specified output width and preserves sign
-- statement:
--   For any natural dimension n and precision q, an integer coordinate z of absolute value at most 2^q satisfies |nz| < 2^(q+lg(n)+1). If n is positive, nz is negative exactly when z is negative. Here lg(n) is the ceiling binary logarithm, bounded below by one. Thus the scaler output sign-magnitude field has sufficient width, including the boundary magnitude.
-- source:
--   Exact coordinate scaling for the integer multiplication to finite-precision DFT mission.

import Definitions.Def_BitDFT_Numerics
open BitDFT IntMul

theorem BitDFT.scalar_product_width (n q : ℕ) (z : ℤ) (hz : z.natAbs ≤ 2^q) :
    ((n : ℤ)*z).natAbs < 2^(q+lg n+1) ∧
    (0 < n → (((n : ℤ)*z < 0) ↔ z < 0)) := by sorry
