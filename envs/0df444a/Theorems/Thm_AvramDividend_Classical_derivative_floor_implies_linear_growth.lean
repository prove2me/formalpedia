-- Prove2me | Theorems.Thm_AvramDividend_Classical_derivative_floor_implies_linear_growth
-- name    : AvramDividend.Classical.derivative_floor_implies_linear_growth
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T23:21:10.666023+00:00
-- url     : https://prove2.me/theorems/9ece73de-ae26-4a66-ae2d-548859a5197c
-- title:
--   Linear lower bound from the marginal-dividend derivative inequality
-- statement:
--   A continuously differentiable interior candidate verification function with derivative at least one between initial capital zero and a must dominate immediate liquidation: w(a) >= a, provided w(0) >= 0. Uses continuity on the closed interval and interior differentiability; includes a=0 and the finite upper endpoint.
-- source:
--   Analytic consequence of the dividend HJB inequality 1-w' ≤ 0 in Eq. (5.8) of Avram–Palmowski–Pistorius (2007), used to show positivity of the candidate verification function; general mean-value theorem on [0,a]. Supports the Ito/localisation obligation AvramDividend.Classical.admissible_cap_dividendValue_le.

import Mathlib

open Set

theorem AvramDividend.Classical.derivative_floor_implies_linear_growth
    (w : ℝ → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hcont : ContinuousOn w (Icc 0 a))
    (hdiff : DifferentiableOn ℝ w (Ioo 0 a))
    (hderiv : ∀ y ∈ Ioo (0 : ℝ) a, 1 ≤ deriv w y)
    (hw0 : 0 ≤ w 0) : a ≤ w a := by sorry
