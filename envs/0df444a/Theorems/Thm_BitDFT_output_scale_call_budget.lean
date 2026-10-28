-- Prove2me | Theorems.Thm_BitDFT_output_scale_call_budget
-- name    : BitDFT.output_scale_call_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T00:09:27.005126+00:00
-- url     : https://prove2.me/theorems/021f73c1-cd3f-4b02-881d-7c5f493d453a
-- title:
--   Budget two q-bit multiplier calls per scaled coefficient
-- statement:
--   For any correct integer multiplier with pointwise runtime bound T and positive vector length n and precision q, two clean q-bit multiplier calls for each real and imaginary coefficient, together with linear tape work, fit within a fixed constant times the transfer cost T(nq)+nT(q)+q ell(q)^2+nq. No monotonicity or regularity assumption on T is needed.
-- source:
--   Runtime accounting for the coordinate-by-coordinate implementation of exact output scaling in the multiplication-to-DFT transfer theorem.

import Definitions.Def_BitDFT_Numerics
set_option autoImplicit false
open BitDFT IntMul

theorem BitDFT.output_scale_call_budget (M : MultitapeTM) (T : ℕ → ℝ) (hM : Multiplier M T)
    (n q : ℕ) (hn : 1 ≤ n) (hq : 1 ≤ q) :
    72 * (n : ℝ) * T q + 1000 * (n : ℝ) * q ≤
      1000 * transferCost T n q := by sorry
