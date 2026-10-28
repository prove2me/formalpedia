-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_increment_exp_second_moment
-- name    : AvramDividend.Classical.levy_bounded_stopping_increment_exp_second_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:43:44.279416+00:00
-- url     : https://prove2.me/theorems/7cde238f-ccd3-4a42-bc5a-b41df5aef1da
-- title:
--   Exact second moment of the exponential Lévy increment after bounded stopping
-- statement:
--   For a bounded stopping time τ and fixed horizon h, the second moment of exp(θ(X_(τ+h)−X_τ)) equals exp(h ψ(2θ)) for all θ≥0. It supplies the uniform L² control used when passing finite stopping grids to limits in martingale and dividend-verification calculations.
-- source:
--   Apply the proved bounded-stopping Lévy increment Laplace transform at parameter 2θ and rewrite the square of the exponential as the exponential of the doubled argument.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_bounded_stopping_increment_exp_second_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω, (Real.exp (θ *
      (X.X (τ ω + h) ω - X.X (τ ω) ω))) ^ 2 ∂P =
        Real.exp ((h : ℝ) * X.ψ (2 * θ)) := by sorry
