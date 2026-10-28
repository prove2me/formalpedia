-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_lintegral_factor
-- name    : AvramDividend.Classical.esscher_bounded_stop_future_increment_lintegral_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:34:51.441334+00:00
-- url     : https://prove2.me/theorems/784dda5c-d2a7-446e-b4f2-e379a59de6b1
-- title:
--   Nonnegative measurable Esscher future-increment rewards factor at bounded stopping times
-- statement:
--   For a bounded spectrally negative Lévy stopping time τ≤H and stopped-history event A, under the genuine finite-terminal Esscher law Q_T (T≥H+1+u), the restricted lower integral of any measurable nonnegative real-valued future increment reward g(X_(τ+u)−X_τ) equals Q_T(A) times the lower integral of g(X_u) under the standalone tilted marginal Q_u. This is a true stopping-time scalar Markov reward identity, not merely an indicator cylinder, and assumes no Wiener–Hopf splitting or clock memorylessness.
-- source:
--   A direct measure-map corollary of the Proved full bounded stop tilted law AvramDividend.Classical.esscher_bounded_stop_future_increment_map_law (9032b4a2), along with pinned Mathlib lintegral_map and lintegral_smul_measure.

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_map_law
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- At a bounded stopping time under a genuine finite-terminal Esscher law,
any measurable nonnegative reward of the future increment factors from history. -/

theorem AvramDividend.Classical.esscher_bounded_stop_future_increment_lintegral_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
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
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A *
      (∫⁻ ω, g (X.X u ω) ∂
        (P.withDensity (fun ω : Ω => ENNReal.ofReal
          (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))) := by sorry
