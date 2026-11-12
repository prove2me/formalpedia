-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger79_original_gaussian_cell_discount_taylor_identity
-- name    : AvramDividend.Classical.avram_gledger79_original_gaussian_cell_discount_taylor_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T08:23:33.012492+00:00
-- url     : https://prove2.me/theorems/48987aa0-4be5-45a7-b1bc-88b54c227501
-- title:
--   Exact original clipped Gaussian cell discount and second-order Taylor residual decomposition
-- statement:
--   Exact finite-cell algebraic expansion of the original discounted postpayment source increment minus the Gaussian linear/quadratic centred noise and generator drift, into discount discretisation, discount cross, full second-order Taylor remainder and drift-quadratic error. This is the local algebra step needed to prove original gledger50, with no stochastic or smoothness assumptions.
-- source:
--   Derived for gledger50 42465e5f, original physical source S, centred M and generator drift G. Identical formula verified by symbolic computation independently.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_gledger79_original_gaussian_cell_discount_taylor_identity
    (E F W Wh a b c z Δ v q : ℝ) :
    ((F - E) * W + F * (Wh - W)) -
      E * (a * z + (b / 2) * (z ^ 2 - Δ * v)) -
      Δ * E * (a * c + (b / 2) * v - q * W) =
    (F - E + q * Δ * E) * W +
      (F - E) * (Wh - W) +
      E * (Wh - W - a * (z + c * Δ) -
        (b / 2) * (z + c * Δ) ^ 2) +
      E * b * (c * Δ * z + c ^ 2 * Δ ^ 2 / 2) := by sorry
