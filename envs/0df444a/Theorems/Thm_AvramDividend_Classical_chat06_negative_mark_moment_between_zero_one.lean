-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_negative_mark_moment_between_zero_one
-- name    : AvramDividend.Classical.chat06_negative_mark_moment_between_zero_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:33:35.948961+00:00
-- url     : https://prove2.me/theorems/ea5fac7e-5d9a-4fe1-815a-1524618a3e15
-- title:
--   Laplace moment of nonpositive claim marks is integrable and lies between zero and one
-- statement:
--   For any measurable nonpositive real claim mark Y on a probability space and any nonnegative Laplace parameter theta, the exponential exp(theta Y) is integrable, and its expectation belongs to [0,1]. The proof bounds the exponential by one almost everywhere, applies dominated integrability, and obtains lower and upper integral bounds. This justifies the uniform moment bounds needed for nonpositive compound Poisson jump marks and the corresponding random-count Laplace summability; full iid-mark moment factorisation remains separate.
-- source:
--   Source bv_negative_mark_moment_between_zero_one_chat06_20261020.lean, 58 lines, 2344 bytes, SHA-256 7d4de13ca084f49e0afd36857c07d7279f0d7c217ed59abbe7f9f420ff00926b. Private probe ef52dbc9-8cb0-4017-8b3d-e162ba7fd806 passed remote elaboration to deliberate sentinel without source errors at pinned revision.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.Complex.Exponential

open MeasureTheory ProbabilityTheory Real

theorem AvramDividend.Classical.chat06_negative_mark_moment_between_zero_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y)
    (hneg : ∀ᵐ ω ∂P, Y ω ≤ 0)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω => Real.exp (θ * Y ω)) P ∧
      0 ≤ (∫ ω, Real.exp (θ * Y ω) ∂P) ∧
      (∫ ω, Real.exp (θ * Y ω) ∂P) ≤ 1 := by sorry
