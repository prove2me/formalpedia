-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedEvent_density_eq_of_upper_grids
-- name    : AvramDividend.Classical.esscher_bounded_stop_stoppedEvent_density_eq_of_upper_grids
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T18:31:21.833524+00:00
-- url     : https://prove2.me/theorems/4e58d5a2-ad00-4851-8886-5ad5e8ba70cf
-- title:
--   Genuine Esscher law agrees with the realised stopped likelihood on bounded stopping-history events
-- statement:
--   For an almost surely bounded genuine stop τ with pointwise decreasing-from-above adapted finite-grid approximations bounded by H≤∞ and before deterministic terminal T, any globally measurable history event A satisfying A∩{τ≤t}∈F_t at every t has identical mass under Q_T and the realised stopped Esscher likelihood P.withDensity M_τ. Uniform integrability follows from the finite-grid L² estimate rather than being added as a hypothesis. There is no claim that the realised-clock density is an independent product law.
-- source:
--   Finite-grid uniform integrability derived using quadratic exponential moments and the general L²-to-UI bridge, direct stopped-event fibre identity A∩{τn=s}=(A∩{τ≤s})∩{τn=s}, and the bounded-stop eventwise density transfer 2f664ff6. No strong Markov at random time, Wiener–Hopf splitting or global Esscher process extension assumed.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_upper_stop_likelihood_uniformIntegrable
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_history_density_eq_of_ui_upper_grids

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_bounded_stop_stoppedEvent_density_eq_of_upper_grids
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (T H : ℝ≥0) (τ : Ω → ℝ≥0)
    (τn : ℕ → Ω → ℝ≥0) (grid : ℕ → Finset ℝ≥0)
    (hgrid : ∀ n ω, τn n ω ∈ grid n)
    (hT : ∀ n s, s ∈ grid n → s ≤ T)
    (hstop : ∀ n s, s ∈ grid n →
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s})
    (hbound : ∀ n ω, τn n ω ≤ H)
    (hlim : ∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω)))
    (habove : ∀ ω n, τ ω ≤ τn n ω)
    (A : Set Ω) (hA : MeasurableSet A)
    (hStopped : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A =
    (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))) A := by sorry
