-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_stopped_likelihood_lintegral_factor
-- name    : AvramDividend.Classical.esscher_bounded_stop_future_increment_stopped_likelihood_lintegral_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T19:08:50.009662+00:00
-- url     : https://prove2.me/theorems/39be5ad9-9a15-4749-8253-965e4d7a7a7e
-- title:
--   Nonnegative tilted future-increment reward factorisation with genuine bounded stopped-likelihood history mass
-- statement:
--   For genuine bounded stopping time τ and a stopped-history event A, the nonnegative Lebesgue integral of any measurable reward g of X_(τ+u)−Xτ under the actual finite-terminal tilted law Q_T, restricted to A, equals the realised stopped-likelihood mass (P.withDensity Mτ)(A) times the Q_u reward integral g(X_u). Both integrals may be infinite and the identity is a genuine finite-terminal tilted Markov reward law, not an independent future law of P.withDensity Mτ.
-- source:
--   Combine accepted bounded genuine-stop tilted future increment reward factorisation 784dda5c and accepted direct bounded stopped-history Esscher density equality 47b25ea7. No division at diverging moments or assumption of Wiener–Hopf independence.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_lintegral_factor
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_density_eq

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_bounded_stop_future_increment_stopped_likelihood_lintegral_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (u T : ℝ≥0) (hT : H + 1 + u ≤ T)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω in A,
      g (X.X (τ ω + u) ω - X.X (τ ω) ω) ∂
        (P.withDensity (fun ω : Ω => ENNReal.ofReal
          (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))) A *
      (∫⁻ ω, g (X.X u ω) ∂
        (P.withDensity (fun ω : Ω => ENNReal.ofReal
          (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))) := by sorry
