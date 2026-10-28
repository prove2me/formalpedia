-- Prove2me | Theorems.Thm_BitDFT_scaled_product_word_direct
-- name    : BitDFT.scaled_product_word_direct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T19:15:34.122701+00:00
-- url     : https://prove2.me/theorems/cee81ab0-2eca-4ddb-9f96-96a4f45b90f3
-- title:
--   Widen the q-bit product to the exact output width
-- statement:
--   Suppose q≥lg(n)+1 and n≤2^lg(n). For every a≤2^q, the product n(a mod 2^q) fits in q+lg(n)+1 bits. Its 2q-bit binary encoding is exactly leading zero padding followed by its encoding at that output width. Thus the clean multiplier result can be converted to the scaler’s output width by removing its known leading zeroes.
-- source:
--   Exact scalar-product serialization for the integer multiplication to finite-precision DFT transfer.

import Definitions.Def_IntMul_MultitapeModel
open IntMul

theorem BitDFT.scaled_product_word_direct (q n a : ℕ) (hq : lg n+1 ≤ q) (hn : n ≤ 2^lg n) (ha : a ≤ 2^q) :
    n*(a%2^q) < 2^(q+lg n+1) ∧
    bin (2*q) (n*(a%2^q)) =
      List.replicate (2*q-(q+lg n+1)) false ++ bin (q+lg n+1) (n*(a%2^q)) := by sorry
