-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_polynomial_geometric_majorant_conversion
-- name    : AvramDividend.Classical.causal_polynomial_geometric_majorant_conversion
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:48:03.538876+00:00
-- url     : https://prove2.me/theorems/859fcce7-2f9d-44db-9814-60ce1ee315f6
-- title:
--   Convert n+1 quadratic-geometric bounds into the C1-series majorant
-- statement:
--   For nonnegative coefficients A,B and 0≤r≤1, the factor (A(n+1)^2+B)r^(n+1) is bounded by (2A+B)(n²+1)r^n. This matches the derivative majorant required by the proved smooth Neumann-series criterion.
-- source:
--   Quadratic inequality (n+1)^2 ≤ 2(n²+1) and monotonicity of rⁿ for 0≤r≤1.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Theorems.Thm_AvramDividend_Classical_causal_polynomial_geometric_derivative_series_C1

open AvramDividend.Classical

theorem AvramDividend.Classical.causal_polynomial_geometric_majorant_conversion
    (n : ℕ) (A B r : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (A * (n + 1 : ℝ) ^ 2 + B) * r ^ (n + 1) ≤
      (2 * A + B) * ((n : ℝ) ^ 2 + 1) * r ^ n := by sorry
