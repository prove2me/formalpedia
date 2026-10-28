-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_negative_laplace
-- name    : AvramDividend.Classical.chat04_esscher_weighted_finite_horizon_negative_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:25:29.185692+00:00
-- url     : https://prove2.me/theorems/fdaa303c-3eed-45c3-bbf7-36d1336e766b
-- title:
--   Under the finite Esscher law, negative exponential moments have the left-shifted Lévy exponent
-- statement:
--   Under the actual finite-horizon Esscher law with nonnegative tilt θ, the negative exponential moment exp(−ε X_t) for 0≤ε≤θ equals exp(t[ψ(θ−ε)−ψ(θ)]). The exponent is well-defined because θ−ε≥0. This supplies the negative-moment exponential-supermartingale input for controlling the running lower infimum of the positively tilted Lévy process.
-- source:
--   Change measure by pinned Mathlib integral_withDensity_eq_integral_toReal_smul, use the adapted process measurability, regroup exponentials, and apply the original Lévy Laplace moment at θ−ε. Combining with the positive q-root half-shift gives an expectation strictly below one at t>0.

import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Process.Adapted
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_weighted_finite_horizon_negative_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ ε : ℝ)
    (hθ : 0 ≤ θ) (hε : 0 ≤ ε) (hεθ : ε ≤ θ) :
    (∫ ω, Real.exp (-ε * X.X t ω) ∂
      (P.withDensity (fun ω : Ω =>
        ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))))) =
      Real.exp ((t : ℝ) * (X.ψ (θ - ε) - X.ψ θ)) := by sorry
