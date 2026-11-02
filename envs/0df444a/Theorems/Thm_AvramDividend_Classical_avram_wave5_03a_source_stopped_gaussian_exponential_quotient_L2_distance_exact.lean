-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_stopped_gaussian_exponential_quotient_L2_distance_exact
-- name    : AvramDividend.Classical.avram_wave5_03a_source_stopped_gaussian_exponential_quotient_L2_distance_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:26:28.569715+00:00
-- url     : https://prove2.me/theorems/d6460b06-83ae-4fab-b193-f169d660112d
-- title:
--   Exact same-source stopped Gaussian exponential difference-quotient L2 distance
-- statement:
--   For the original bounded-stopped pure-Gaussian spectrally negative Levy path, the L2 distance squared between two cumulant-centred exponential quotients at nonnegative parameters θ,η equals the exact sum of their source variances minus twice their source covariance: (exp(hσ²θ²)-1)/θ²+(exp(hσ²η²)-1)/η²−2(exp(hσ²θη)-1)/(θη). This uses original P, original stopped path, source quotient MemLp 2 and the previously Proved same-source Gram kernel, without any detached Brownian process. The exact two-parameter distance identity supplies the key Cauchy-family input for a future original-source continuous-martingale construction, but does not itself assert convergence or a quadratic-variation process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_stopped_gaussian_exponential_quotient_centered_L2
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_stopped_gaussian_exponential_quotient_cross_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_gaussian_stopped_exponential_rescaled_energy_export

open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_source_stopped_gaussian_exponential_quotient_L2_distance_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ η : ℝ) (hθ : 0 ≤ θ) (hη : 0 ≤ η) :
    let Z : ℝ → Ω → ℝ := fun ξ ω =>
      (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ ξ) - 1) / ξ
    (∫ ω, (Z θ ω - Z η ω) ^ 2 ∂P) =
      (Real.exp ((h : ℝ) * (X.σ ^ 2 * θ ^ 2)) - 1) / θ ^ 2 +
      (Real.exp ((h : ℝ) * (X.σ ^ 2 * η ^ 2)) - 1) / η ^ 2 -
      2 * ((Real.exp ((h : ℝ) * (X.σ ^ 2 * θ * η)) - 1) / (θ * η)) := by
  sorry
