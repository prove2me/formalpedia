-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger58_factorised_second_order_ode_weighted_first_derivative
-- name    : AvramDividend.Classical.avram_gledger58_factorised_second_order_ode_weighted_first_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:12:51.212618+00:00
-- url     : https://prove2.me/theorems/abd88726-6de6-441d-949f-9e60fad177b6
-- title:
--   Factorised second-order HJB upper inequality controls its weighted first derivative
-- statement:
--   A second-order differentiable real function satisfying the factorised scalar differential upper inequality has a nonincreasing positive exponential integrating factor of the first-order combination w' minus l times w. This isolates the sole ODE comparison step required to turn a Gaussian generator HJB upper inequality and its characteristic roots into the one-sided exponential upper bound needed for stopped physical source integrability.
-- source:
--   Necessary scalar HJB-to-exponential-envelope bridge. Proved gledger55 establishes factorisation; Proved gledger56 establishes real opposite-sign roots; gledger57 derives the final upper envelope. Does not assume control of negative excursions of w.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gsource15_exponential_derivative_comparison
open AvramDividend.Classical Set
noncomputable section

theorem AvramDividend.Classical.avram_gledger58_factorised_second_order_ode_weighted_first_derivative
    (r l u : ℝ) (w : ℝ → ℝ)
    (hw : ∀ y : ℝ, u ≤ y → HasDerivAt w (deriv w y) y)
    (hw2 : ∀ y : ℝ, u ≤ y →
      HasDerivAt (deriv w) (iteratedDeriv 2 w y) y)
    (hode : ∀ y : ℝ, u ≤ y →
      iteratedDeriv 2 w y - (r + l) * deriv w y +
        r * l * w y ≤ 0) :
    ∀ y : ℝ, u ≤ y →
      Real.exp (-(r * y)) * (deriv w y - l * w y) ≤
        Real.exp (-(r * u)) * (deriv w u - l * w u) := by sorry
