-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_gaussian_zero_ladder_renewal_measure_exists
-- name    : AvramDividend.Classical.avram_p4_f6_gaussian_zero_ladder_renewal_measure_exists
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T10:14:21.156276+00:00
-- url     : https://prove2.me/theorems/e19eb951-1976-4fde-a73c-49390524d288
-- title:
--   Atomless locally finite ladder-height renewal measure with theta-over-psi transform
-- statement:
--   Construct the original Gaussian spectrally-negative Lévy descending ladder-height renewal measure ν, supported on strictly positive reserves, atomless and locally finite, with transform θ/ψ(θ). This Wiener-Hopf fluctuation-theory existence step is independent of subsequently taking its cumulative distribution to obtain the zero-scale W.
-- source:
--   Wiener-Hopf factorisation: ψ(θ)/θ is the killed descending ladder-height Bernstein exponent after the appropriate Esscher shift. Its potential measure has Laplace transform θ/ψ(θ) and the strictly positive Gaussian drift makes it atomless. This is the central source existence step for the q=0 scale; Kuznetsov, Kyprianou, Rivero (2011), Theory of Scale Functions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f6_gaussian_zero_ladder_renewal_measure_exists
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hσ : 0 < X.σ) :
    ∃ ν : Measure ℝ,
      (ν (Iic (0 : ℝ)) = 0) ∧
      (∀ x : ℝ, ν {x} = 0) ∧
      (∀ x : ℝ, 0 ≤ x → ν (Ioc (0 : ℝ) x) < ⊤) ∧
      (∀ θ : ℝ, 0 ≤ θ → 0 < X.ψ θ →
      IntegrableOn (fun y : ℝ => Real.exp (-(θ * y))) (Ioi 0) ν ∧
      ∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) ∂ν = θ / X.ψ θ) := by sorry
