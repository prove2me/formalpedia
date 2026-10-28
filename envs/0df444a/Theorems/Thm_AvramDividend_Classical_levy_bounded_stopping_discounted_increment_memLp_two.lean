-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_increment_memLp_two
-- name    : AvramDividend.Classical.levy_bounded_stopping_discounted_increment_memLp_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:03:14.553698+00:00
-- url     : https://prove2.me/theorems/11edac20-85d1-4b3a-809e-618cdd1115a4
-- title:
--   L² bound for discounted Lévy exponential increments after bounded stopping
-- statement:
--   For a bounded stopping time and any real discount rate q, the discounted exponential of the future Lévy increment is an L² random variable at every nonnegative Laplace parameter θ. This permits Cauchy-Schwarz and dominated estimates for discounted dividend payoffs.
-- source:
--   Use the already proved L² membership of the un-discounted post-stopping exponential and stability of MemLp under multiplication by a deterministic real constant.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_increment_exp_memLp_two
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_bounded_stopping_discounted_increment_memLp_two
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ q : ℝ) (hθ : 0 ≤ θ) :
    MemLp (fun ω => Real.exp (-(q * (h : ℝ))) *
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω))) 2 P := by sorry
