-- Prove2me | Theorems.Thm_BitDFT_packed_scale_runtime_budget
-- name    : BitDFT.packed_scale_runtime_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T21:58:39.893752+00:00
-- url     : https://prove2.me/theorems/eb740586-27b2-41c7-a4e3-39cab18e4a16
-- title:
--   Budget fixed packed scaling calls by the exact transfer cost
-- statement:
--   For every correct integer multiplier with pointwise bound T, and positive n and q, ten calls at size nq, twenty-two calls at size q, and 1000nq linear transitions are bounded by 1000 times the stated transfer cost. This estimate requires no monotonicity or regularity of T.
-- source:
--   Runtime accounting for blockwise exact scaling of the real and imaginary output streams. Large vectors use a constant number of nq-bit packed products; the finite small-dimension case uses at most a constant number of q-bit products per coordinate.

import Definitions.Def_BitDFT_Numerics
set_option autoImplicit false
open BitDFT IntMul

theorem BitDFT.packed_scale_runtime_budget (M : MultitapeTM) (T : ℕ → ℝ) (hM : Multiplier M T)
    (n q : ℕ) (hn : 1 ≤ n) (hq : 1 ≤ q) :
    10 * T (n*q) + 22 * T q + 1000 * (n : ℝ) * q ≤
      1000 * transferCost T n q := by sorry
