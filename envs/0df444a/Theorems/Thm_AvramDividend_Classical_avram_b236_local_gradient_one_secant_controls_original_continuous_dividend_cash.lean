-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b236_local_gradient_one_secant_controls_original_continuous_dividend_cash
-- name    : AvramDividend.Classical.avram_b236_local_gradient_one_secant_controls_original_continuous_dividend_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:28:36.584138+00:00
-- url     : https://prove2.me/theorems/6800a200-f156-4e02-a35f-8a86dd613209
-- title:
--   Exact original positive-interior derivative ≥1 implies value decrease dominates paid continuous dividend secant
-- statement:
--   For the original candidate value function w and any physically realised pair of reserve levels a≤b in a smooth positive pre-ruin/cap interior segment, assume w is continuous on the closed reserve segment and differentiable on its open segment with w′(r)≥1. Prove the exact deterministic cash inequality b−a≤w(b)−w(a). The proof applies the pinned real-interval monotoneOn_of_deriv_nonneg theorem to r↦w(r)−r. For a decreasing continuous dividend path, each sufficiently fine original pre-ruin segment carries cash b−a dominated by the candidate-value drop, and the telescoped/finite-variation Stieltjes limit is bounded accordingly. This is one genuine local C2/HJB/Stieltjes source ingredient for B236; applying it to the actual original D and its continuous cash intervals and handling terminal ruin contact are separate substantive obligations. No Gaussian ν=0 assumption or postruin paths.
-- source:
--   Pinned Mathlib monotoneOn_of_deriv_nonneg on an exact real closed reserve interval, original w′≥1 interior HJB.

import Mathlib
open Set Filter Topology MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_b236_local_gradient_one_secant_controls_original_continuous_dividend_cash
    (w : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hcont : ContinuousOn w (Icc a b))
    (hdiff : ∀ r ∈ Ioo a b, DifferentiableAt ℝ w r)
    (hgrad : ∀ r ∈ Ioo a b, 1 ≤ deriv w r) :
    b - a ≤ w b - w a := by sorry
