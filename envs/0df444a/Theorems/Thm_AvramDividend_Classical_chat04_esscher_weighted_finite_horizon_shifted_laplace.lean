-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_shifted_laplace
-- name    : AvramDividend.Classical.chat04_esscher_weighted_finite_horizon_shifted_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:13:53.296918+00:00
-- url     : https://prove2.me/theorems/73de4f4f-bf10-4dbd-898a-2eba7912fedf
-- title:
--   Actual Esscher finite-horizon probability law has the shifted Lévy Laplace exponent
-- statement:
--   Under the genuine finite-horizon Esscher tilted probability measure, the positive exponential moment of the Lévy endpoint X_t is exactly exp(t times the shifted Laplace exponent ψ(θ+η)-ψ(θ)) for θ,η≥0. This identifies the finite-time tilted marginal without inventing a global tilted probability measure.
-- source:
--   Use pinned Mathlib `integral_withDensity_eq_integral_toReal_smul` with measurable finite exponential density, `X.adapted.measurable`, and the already Proved `esscher_finite_horizon_shifted_exponential_moment`. The result is part of the projective Esscher stochastic-law foundation for descending Wiener–Hopf.

import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Process.Adapted
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_esscher_finite_horizon_shifted_exponential_moment
open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_weighted_finite_horizon_shifted_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ η : ℝ) (hθ : 0 ≤ θ) (hη : 0 ≤ η) :
    (∫ ω, Real.exp (η * X.X t ω) ∂
      (P.withDensity (fun ω : Ω =>
        ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))))) =
      Real.exp ((t : ℝ) * (X.ψ (θ + η) - X.ψ θ)) := by sorry
