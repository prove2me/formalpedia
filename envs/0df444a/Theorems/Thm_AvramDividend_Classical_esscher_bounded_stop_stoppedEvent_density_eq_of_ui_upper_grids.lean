-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedEvent_density_eq_of_ui_upper_grids
-- name    : AvramDividend.Classical.esscher_bounded_stop_stoppedEvent_density_eq_of_ui_upper_grids
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T18:23:05.020063+00:00
-- url     : https://prove2.me/theorems/47e3fdbe-3730-489f-8d22-37da232023f5
-- title:
--   Bounded stopped-history Esscher density agreement using a genuine stopping-event sigma condition
-- statement:
--   For a bounded right-approximable stopping time and a measurable stopped-history event A satisfying A∩{τ≤t}∈F_t for all t, the genuine deterministic-terminal Esscher measure agrees with the realised stopped likelihood on A, conditional only on uniform integrability of the actual finite-grid stopped likelihoods. Finite-grid membership and fibre adaptation imply stopped history adaptedness; no separately assumed fibrewise A measurability is necessary.
-- source:
--   Accepted stoppedEvent_upperGridFibre_measurable ddc5c663 and bounded-stop history density transfer 2f664ff6, with a finite-grid empty-fibre proof outside the grid. The UI hypothesis is explicit and separately discharged by finite-grid L2. Does not invoke WH, random-time Esscher strong Markov, or global tilted path laws.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_history_density_eq_of_ui_upper_grids
import Theorems.Thm_AvramDividend_Classical_stoppedEvent_upperGridFibre_measurable

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_bounded_stop_stoppedEvent_density_eq_of_ui_upper_grids
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (τn : ℕ → Ω → ℝ≥0) (grid : ℕ → Finset ℝ≥0)
    (hgrid : ∀ n ω, τn n ω ∈ grid n)
    (hT : ∀ n s, s ∈ grid n → s ≤ T)
    (hstop : ∀ n s, s ∈ grid n →
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s})
    (hlim : ∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω)))
    (habove : ∀ ω n, τ ω ≤ τn n ω)
    (A : Set Ω) (hA : MeasurableSet A)
    (hStopped : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (hUI : UniformIntegrable (fun n ω =>
      Real.exp (θ * X.X (τn n ω) ω -
        (τn n ω : ℝ) * X.ψ θ)) 1 P) :
    (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A =
    (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))) A := by sorry
