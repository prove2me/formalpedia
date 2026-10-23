-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_global_weighted_norm_bddAbove
-- name    : AvramDividend.Classical.scaleFunction_global_weighted_norm_bddAbove
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T19:01:47.41825+00:00
-- url     : https://prove2.me/theorems/b9952447-4e50-45c3-b46c-1456f6ce144e
-- title:
--   Scale function's exponential Laplace damping is globally bounded
-- statement:
--   For any q-scale function W, θ≥0 and ψ(θ)>q, the exponentially damped scale function y↦exp(−θy)W(y) has globally bounded absolute value on ℝ. W is nonnegative by its monotonicity and vanishing for negative arguments. A previously Proved pointwise Laplace envelope gives exp(−θ(y+1))W(y)≤1/(ψ(θ)−q); multiplying by exp θ gives the uniform bound exp θ/(ψ(θ)−q). This bound is exactly what's needed to replace localising convolutions by a globally bounded exponentially damped Esscher kernel.
-- source:
--   Proved chat03_scale_global_weighted_exponential_bound and scaleFunction_monotone

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_chat03_scale_global_weighted_exponential_bound
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_global_weighted_norm_bddAbove
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ) :
    BddAbove (Set.range (fun y : ℝ =>
      ‖Real.exp (-(θ * y)) * W y‖)) := by sorry
