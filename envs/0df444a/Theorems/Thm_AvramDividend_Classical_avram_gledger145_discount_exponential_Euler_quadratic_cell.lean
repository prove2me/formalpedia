-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger145_discount_exponential_Euler_quadratic_cell
-- name    : AvramDividend.Classical.avram_gledger145_discount_exponential_Euler_quadratic_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:53:04.839217+00:00
-- url     : https://prove2.me/theorems/d5ddbba4-4d2b-4c19-8c67-8a1d8a76cc05
-- title:
--   Uniform second-order discounted exponential Euler error on a deterministic Gaussian mesh cell
-- statement:
--   For nonnegative discount q, nonnegative cell origin t and width δ, with qδ at most one, the one-cell discount Euler error has absolute value at most q squared δ squared. This deterministic quadratic estimate controls interior cells of the original clipped Gaussian discount-clock L1 child gledger139.
-- source:
--   Pinned Mathlib Real.abs_exp_sub_one_sub_id_le with argument -qδ, exponential additivity, exp(-qt) between zero and one, and algebra.

import Mathlib
open Real
noncomputable section

theorem AvramDividend.Classical.avram_gledger145_discount_exponential_Euler_quadratic_cell
    (q t δ : ℝ) (hq : 0 ≤ q) (ht : 0 ≤ t)
    (hδ : 0 ≤ δ) (hsmall : q * δ ≤ 1) :
    |Real.exp (-(q * (t + δ))) - Real.exp (-(q * t)) +
        q * δ * Real.exp (-(q * t))| ≤ (q * δ) ^ 2 := by sorry
