-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a54_construct_zero_nu_levy_on_identical_raw_filtration_20261114
-- name    : AvramDividend.Classical.avram_a54_construct_zero_nu_levy_on_identical_raw_filtration_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:14:51.959022+00:00
-- url     : https://prove2.me/theorems/84350443-1c23-46b4-86ee-5db58bcbb25c
-- title:
--   Zero-Levy-measure source constructor preserving the identical raw filtered probability space
-- statement:
--   A zero-start, allpath cadlag/no-positive-jump real source with raw adaptedness, stationary independent increments and Gaussian positive Laplace moments is a zero-jump spectrally negative Levy process on the unchanged filtration.
-- source:
--   Exact SpectrallyNegativeLevy definition and zero-measure integral.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a54_construct_zero_nu_levy_on_identical_raw_filtration_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (G : ℝ≥0 → Ω → ℝ) (σ : ℝ)
    (hP : IsProbabilityMeasure P) (hσ : 0 ≤ σ)
    (hZero : ∀ ω, G 0 ω = 0)
    (hRight : ∀ ω t, ContinuousWithinAt (fun u => G u ω) (Ici t) t)
    (hLeft : ∀ ω t, 0 < t →
      ∃ l, Tendsto (fun u : ℝ≥0 => G u ω) (𝓝[<] t) (𝓝 l))
    (hNoPositive : ∀ ω t l, 0 < t →
      Tendsto (fun u : ℝ≥0 => G u ω) (𝓝[<] t) (𝓝 l) →
      G t ω ≤ l)
    (hAdapt : Adapted 𝓕 G)
    (hIndep : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap
        (fun ω => G t ω - G s ω) inferInstance) (𝓕 s) P)
    (hStat : ∀ s t, s ≤ t →
      IdentDistrib (fun ω => G t ω - G s ω) (G (t - s)) P P)
    (hLap : ∀ (t : ℝ≥0) (θ : ℝ), 0 ≤ θ →
      Integrable (fun ω => Real.exp (θ * G t ω)) P ∧
      (∫ ω, Real.exp (θ * G t ω) ∂P) =
        Real.exp ((t : ℝ) * (σ ^ 2 * θ ^ 2 / 2))) :
    ∃ Y : SpectrallyNegativeLevy P 𝓕,
      Y.X = G ∧ Y.c = 0 ∧ Y.ν = 0 ∧ Y.σ = σ := by sorry
