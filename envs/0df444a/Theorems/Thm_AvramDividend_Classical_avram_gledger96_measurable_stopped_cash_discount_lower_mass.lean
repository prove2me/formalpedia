-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger96_measurable_stopped_cash_discount_lower_mass
-- name    : AvramDividend.Classical.avram_gledger96_measurable_stopped_cash_discount_lower_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:09:30.846206+00:00
-- url     : https://prove2.me/theorems/dfeb2cca-6b3e-49e7-9aac-96b04baf15b6
-- title:
--   Discounted Stieltjes cash controls the original unweighted mass of a bounded payment set
-- statement:
--   For any measurable set of actual dividend-payment times bounded above by b, the original discounted Stieltjes mass is at least exp(-qb) times the unweighted mass. This is the missing quantitative transfer from the right-endpoint cell's unweighted mesh error to the original strict discounted cash budget. No stochastic assumption or auxiliary process is introduced.
-- source:
--   Sound strictly smaller positive-mass bridge for gledger81, derived by integrating the pointwise deterministic discount bound on the actual payment set.

import Mathlib
namespace AvramDividend
namespace Classical
end Classical
end AvramDividend
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger96_measurable_stopped_cash_discount_lower_mass
    (q : ℝ) (hq : 0 ≤ q) (μ : Measure ℝ)
    (S : Set ℝ) (hS : MeasurableSet S)
    (b : ℝ) (hSb : ∀ t ∈ S, t ≤ b) :
    ENNReal.ofReal (Real.exp (-(q * b))) * μ S ≤
      (∫⁻ t in S, ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) := by sorry
