-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a23_affine_modulus_L1_tendsto_zero
-- name    : AvramDividend.Classical.avram_a23_affine_modulus_L1_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:51:55.420725+00:00
-- url     : https://prove2.me/theorems/2efe1ffb-1119-4ec7-9e71-f462c17f01a7
-- title:
--   Affine epsilon plus vanishing reserve error implies value L1 error vanishes
-- statement:
--   A nonnegative sequence a_m converges to zero if every positive epsilon admits a finite L such that a_m≤epsilon+L b_m and b_m→0. This exactly implements the HJB compact modulus to Gaussian spatial mesh L1 transfer after integration, permitting a short proof of the full stochastic theorem.
-- source:
--   Elementary quantitative convergence helper for genuine stopped Gaussian spatial L1 mesh errors.

import Mathlib
open Filter

theorem AvramDividend.Classical.avram_a23_affine_modulus_L1_tendsto_zero
    (a b : ℕ → ℝ)
    (hb : Tendsto b atTop (nhds (0 : ℝ)))
    (ha : ∀ m, 0 ≤ a m)
    (hBound : ∀ ε : ℝ, 0 < ε → ∃ L : ℝ,
      0 ≤ L ∧ ∀ m, a m ≤ ε + L * b m) :
    Tendsto a atTop (nhds (0 : ℝ)) := by sorry
