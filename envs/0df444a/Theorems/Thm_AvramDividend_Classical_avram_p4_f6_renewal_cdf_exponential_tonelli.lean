-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_renewal_cdf_exponential_tonelli
-- name    : AvramDividend.Classical.avram_p4_f6_renewal_cdf_exponential_tonelli
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T10:21:50.859544+00:00
-- url     : https://prove2.me/theorems/847548b4-661a-414b-994f-5b5a7b87dbf0
-- title:
--   Exponential Laplace transform of cumulative renewal measure by Tonelli
-- statement:
--   Tonelli interchanges ∫exp(-θx)ν((0,x])dx with ∫∫_{y<x} exp(-θx)dx ν(dy), yielding (1/θ)∫exp(-θy)ν(dy)=1/ψ(θ). Positivity ensures integrability, and ψ(θ)>0 implies θ>0 under the spectrally-negative Lévy standing assumptions.
-- source:
--   Tonelli's theorem for a nonnegative exponential kernel and explicit exponential-tail integration. The stationary Lévy Laplace exponent satisfies ψ(0)=0 and convexity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f6_renewal_cdf_exponential_tonelli
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hσ : 0 < X.σ)
    (ν : Measure ℝ)
    (hSupp : ν (Iic (0 : ℝ)) = 0)
    (hFin : ∀ x : ℝ, 0 ≤ x → ν (Ioc (0 : ℝ) x) < ⊤)
    (hLap : ∀ θ : ℝ, 0 ≤ θ → 0 < X.ψ θ →
      IntegrableOn (fun y : ℝ => Real.exp (-(θ * y))) (Ioi 0) ν ∧
      ∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) ∂ν = θ / X.ψ θ) :
    ∀ θ : ℝ, 0 ≤ θ → 0 < X.ψ θ →
      IntegrableOn (fun y : ℝ => Real.exp (-(θ * y)) * (if 0 ≤ y then (ν (Ioc (0 : ℝ) y)).toReal else 0)) (Ioi 0) ∧
      ∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * (if 0 ≤ y then (ν (Ioc (0 : ℝ) y)).toReal else 0) =
      (X.ψ θ)⁻¹ := by sorry
