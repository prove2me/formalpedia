-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_gaussian_ladder_renewal_cdf_laplace
-- name    : AvramDividend.Classical.avram_p4_f6_gaussian_ladder_renewal_cdf_laplace
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T10:14:20.608203+00:00
-- url     : https://prove2.me/theorems/e94805da-daf4-4721-b414-db7b6f5bc503
-- title:
--   Cumulative atomless renewal measure gives a continuous nonnegative reciprocal-Laplace zero-scale inverse
-- statement:
--   Set W₀(x)=ν((0,x]) for x≥0 using ENNReal.toReal. Local finiteness and atomlessness give continuity on the positive half-line, while positivity of ν gives W₀≥0 and zero support for negative arguments. Tonelli and ∫_y^∞ e^(−θx)dx=e^(−θy)/θ convert the ladder renewal transform θ/ψ(θ) into the required W₀ transform 1/ψ(θ). This stage is a measure-theoretic analytic bridge separate from the stochastic Wiener-Hopf construction.
-- source:
--   Elementary Tonelli/Fubini for cumulative locally finite positive measures, exponential tail integration, and continuity of atomless cumulative distributions. The transform is the classical scale-renewal identity in Kuznetsov, Kyprianou, Rivero (2011).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f6_gaussian_ladder_renewal_cdf_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hσ : 0 < X.σ)
    (ν : Measure ℝ)
    (hSupp : ν (Iic (0 : ℝ)) = 0)
    (hAtom : ∀ x : ℝ, ν {x} = 0)
    (hFin : ∀ x : ℝ, 0 ≤ x → ν (Ioc (0 : ℝ) x) < ⊤)
    (hLap : ∀ θ : ℝ, 0 ≤ θ → 0 < X.ψ θ →
      IntegrableOn (fun y : ℝ => Real.exp (-(θ * y))) (Ioi 0) ν ∧
      ∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) ∂ν = θ / X.ψ θ) :
    ∃ W₀ : ℝ → ℝ,
      (∀ y < 0, W₀ y = 0) ∧
      (∀ y, 0 ≤ y → 0 ≤ W₀ y) ∧
      ContinuousOn W₀ (Ici 0) ∧
      (∀ θ : ℝ, 0 ≤ θ → 0 < X.ψ θ →
      IntegrableOn (fun y => Real.exp (-(θ * y)) * W₀ y) (Ioi 0) ∧
      ∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * W₀ y = (X.ψ θ)⁻¹) := by sorry
