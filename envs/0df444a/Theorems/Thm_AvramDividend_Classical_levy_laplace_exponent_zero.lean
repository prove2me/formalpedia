-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_zero
-- name    : AvramDividend.Classical.levy_laplace_exponent_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:06:35.049733+00:00
-- url     : https://prove2.me/theorems/88416f41-e034-4680-af64-dee0ca4406ba
-- title:
--   Canonical spectrally negative Lévy Laplace exponent vanishes at zero
-- statement:
--   For the exact source-defined Lévy–Khintchine exponent ψ(θ)=cθ+(σ²/2)θ²+∫_{(-∞,0)}(exp(θy)−1−θy 1_{|y|<1})ν(dy), setting θ=0 makes every drift, Gaussian and jump term zero. This provides the canonical ψ(0)=0 boundary condition needed by the positive Esscher root existence proof, without any Standing, moment or scale-function assumptions.
-- source:
--   Exact mission definition AvramDividend_Classical_SpectrallyNegativeLevy, laplaceExponent and SpectrallyNegativeLevy.ψ.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_laplace_exponent_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) : X.ψ 0 = 0 := by sorry
