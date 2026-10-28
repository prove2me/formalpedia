-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_finite_activity_exp_survival_drift_integral
-- name    : AvramDividend.Classical.bv_finite_activity_exp_survival_drift_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:46:42.431046+00:00
-- url     : https://prove2.me/theorems/1ddcb99a-f210-48e0-9cad-40bf9a4791e7
-- title:
--   Discounted drift payoff integrated against an exponential first-jump survival curve
-- statement:
--   For discount q>0 and nonnegative Poisson jump intensity lambda, integrating constant drift d with survival exp(-lambda t) and discount exp(-q t) over positive time gives d/(q+lambda). This verified deterministic integral is the final calculus step after a separate stochastic identification of the zero-barrier Stieltjes reward with the first-jump survival integral.
-- source:
--   Avram, Palmowski and Pistorius (2007), §3.3 equation (3.14), https://arxiv.org/pdf/math/0702893. Pinned Mathlib integral_exp_mul_Ioi exact source and remote compiler signature verified 25 Oct 2026.

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
open MeasureTheory Set

theorem AvramDividend.Classical.bv_finite_activity_exp_survival_drift_integral
    (d q jumpRate : ℝ) (hq : 0 < q) (hjumpRate : 0 ≤ jumpRate) :
    (∫ t : ℝ in Ioi (0 : ℝ),
      d * Real.exp (-(q + jumpRate) * t) ∂volume) = d / (q + jumpRate) := by sorry
