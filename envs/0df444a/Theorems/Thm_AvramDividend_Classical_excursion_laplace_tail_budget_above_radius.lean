-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_laplace_tail_budget_above_radius
-- name    : AvramDividend.Classical.excursion_laplace_tail_budget_above_radius
-- status  : Open
-- author  : @WillR
-- created : 2026-10-23T23:52:18.830238+00:00
-- url     : https://prove2.me/theorems/397458b3-aac0-4947-9bc7-83f00e085588
-- title:
--   Laplace tail budget for every radius above the decay threshold
-- statement:
--   If exp(-sR)+δ≤1, the region x>R is contained in the Markov excess set. Consequently the Laplace transform plus δ times the mass above R is at most total mass. This is the tail inequality used to prove uniform tightness from reciprocal lower bounds.
-- source:
--   Direct measure-mono consequence of published excursion_laplace_tail_budget_markov.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Theorems.Thm_AvramDividend_Classical_excursion_laplace_tail_budget_markov
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.excursion_laplace_tail_budget_above_radius
    (μ : Measure ℝ) (s R : ℝ) (hs : 0 < s)
    (hsupport : μ (Iio (0 : ℝ)) = 0)
    (δ : ENNReal)
    (hdecay : ENNReal.ofReal (Real.exp (-(s * R))) + δ ≤ 1) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂μ) +
      δ * μ (Ioi R) ≤ μ Set.univ := by sorry
