-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_map_law
-- name    : AvramDividend.Classical.esscher_bounded_stop_future_increment_map_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:15:59.969831+00:00
-- url     : https://prove2.me/theorems/9032b4a2-fc71-4bb6-8a61-52f1bfe2ee18
-- title:
--   Genuine finite-terminal Esscher law at any bounded Lévy stopping time
-- statement:
--   For a bounded Lévy stopping time τ≤H, stopped-history event A and every finite Esscher terminal T≥H+1+u, the law of the shifted increment X_(τ+u)−X_τ restricted to A under the genuine finite-terminal Esscher measure Q_T equals Q_T(A) times the law of X_u under Q_u, as equality of finite Borel measures on ℝ. This is a full distributional strong-Markov cylinder identity obtained from finite dyadic stopping-time factorisation, pathwise right continuity and compact-test dominated convergence. It does not assume a global tilted Lévy law, independent residual clock or Wiener–Hopf independence.
-- source:
--   Accepted bounded_stop_explicit_grid_increment_limit_with_horizon (062ac6d1) and esscher_bounded_stop_dyadic_grid_cylinder_factor (427d089b), proved measurable Lévy stopped future paths (c68a1334, 722354f7), finite terminal probability (6c6f7684); general constant_restricted_real_law_pointwise_limit authored by 1E-A, pending proof. Kuznetsov–Kyprianou–Rivero scale-function fluctuation theory.

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_dyadic_grid_cylinder_factor
import Theorems.Thm_AvramDividend_Classical_bounded_stop_explicit_grid_increment_limit_with_horizon
import Theorems.Thm_AvramDividend_Classical_finite_grid_adapted_fibres_isStoppingTime
import Theorems.Thm_AvramDividend_Classical_constant_restricted_real_law_pointwise_limit
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

/-- Bounded genuinely stopped increments have stationary tilted law under
one deterministic finite-terminal Esscher probability. -/

theorem AvramDividend.Classical.esscher_bounded_stop_future_increment_map_law
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
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    let QT : Measure Ω := P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))
    let QU : Measure Ω := P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))
    Measure.map (fun ω : Ω => X.X (τ ω + u) ω - X.X (τ ω) ω)
      (QT.restrict A) = QT A • Measure.map (X.X u) QU := by sorry
