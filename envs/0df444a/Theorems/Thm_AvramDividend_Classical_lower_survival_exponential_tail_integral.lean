-- Prove2me | Theorems.Thm_AvramDividend_Classical_lower_survival_exponential_tail_integral
-- name    : AvramDividend.Classical.lower_survival_exponential_tail_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:48:52.236178+00:00
-- url     : https://prove2.me/theorems/90365da5-4c3f-4326-8a48-98d96e72c74b
-- title:
--   Exponential Laplace kernel over the non-ruin initial-reserve interval
-- statement:
--   For a real running-minimum level m and positive Laplace parameter θ, the initial-reserve condition x≥0 and x+m≥0 restricts x to the half-line with lower endpoint max(0,-m). The exponential kernel is integrable there and its integral is exp(-θ max(0,-m))/θ. This permits the killed-survival reserve transform to be converted into an expectation of an exponential function of the running infimum.
-- source:
--   Pinned-Mathlib improper-integral formula integral_exp_mul_Ioi and integrableOn_exp_mul_Ioi. The surviving reserve threshold is max(0,-m).

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory Set

theorem AvramDividend.Classical.lower_survival_exponential_tail_integral
    (m θ : ℝ) (hθ : 0 < θ) :
    IntegrableOn (fun x : ℝ => Real.exp (-θ * x)) (Ioi (max 0 (-m))) ∧
      (∫ x in Ioi (max 0 (-m)), Real.exp (-θ * x)) =
        Real.exp (-θ * max 0 (-m)) / θ := by sorry
