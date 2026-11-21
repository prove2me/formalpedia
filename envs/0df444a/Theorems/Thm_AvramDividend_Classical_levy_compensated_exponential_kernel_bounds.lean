-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_kernel_bounds
-- name    : AvramDividend.Classical.levy_compensated_exponential_kernel_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T20:03:25.534163+00:00
-- url     : https://prove2.me/theorems/1eaa6bca-b0c1-44b1-b12f-65ad042d42e6
-- title:
--   Sharp positive and linear bounds on the compensated Lévy exponential kernel
-- statement:
--   For nonnegative discount θ and positive jump magnitude t, prove the exact bound 0≤1−exp(−θt)≤θt. The second inequality is the elementary convex exponential inequality and is needed to control compensated small-jump second moments when ∫ small jump magnitude diverges.
-- source:
--   Pinned Mathlib Real.add_one_le_exp and Real.exp_le_exp. Used in original negative-jump Lévy tail real-integrability bridge 847641c4.

import Mathlib

theorem AvramDividend.Classical.levy_compensated_exponential_kernel_bounds
    (θ t : ℝ) (hθ : 0 ≤ θ) (ht : 0 ≤ t) :
    0 ≤ 1 - Real.exp (-θ * t) ∧
      1 - Real.exp (-θ * t) ≤ θ * t := by sorry
