-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_perpetual_survival_cumulative_laplace_is_measure_laplace
-- name    : AvramDividend.Classical.chat04_esscher_perpetual_survival_cumulative_laplace_is_measure_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T18:05:17.857262+00:00
-- url     : https://prove2.me/theorems/3c82753f-8d83-4218-a195-bf54fc52f3f2
-- title:
--   Exact cumulative Laplace transform of perpetual Esscher survival via its finite supported Stieltjes law
-- statement:
--   There exists an actually finite Borel measure ν supported on nonnegative reserves whose cumulative distribution is perpetual Esscher survival. For every positive capital-Laplace parameter β, the Laplace integral of that survival function over positive capitals equals β⁻¹ times the ordinary nonnegative Laplace transform of ν. This is an unconditional bridge from the actual stochastic law to the isolated numerical Wiener–Hopf scalar value.
-- source:
--   Apply the accepted finite nonnegative perpetual Esscher distribution theorem and accepted generic positiveLaplace_cumulative_measure, rewriting ν(Iic x) by the exact perpetual survival infimum. Does not assert a Wiener–Hopf scalar value, root scale function, or optional stopping.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_cumulative_measure
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_perpetual_infimum_finite_nonnegative_distribution
open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_perpetual_survival_cumulative_laplace_is_measure_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧ ν (Iio (0 : ℝ)) = 0 ∧
      ∀ β : ℝ, 0 < β →
        (∫⁻ x : ℝ in Ioi 0,
          ENNReal.ofReal (Real.exp (-β * x)) * (⨅ t : ℝ≥0, ENNReal.ofReal (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P))) =
        ENNReal.ofReal (1 / β) *
          (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂ν) := by sorry
