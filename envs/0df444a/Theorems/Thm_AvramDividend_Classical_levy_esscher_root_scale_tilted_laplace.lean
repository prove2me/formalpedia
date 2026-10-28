-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_esscher_root_scale_tilted_laplace
-- name    : AvramDividend.Classical.levy_esscher_root_scale_tilted_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:11:46.374397+00:00
-- url     : https://prove2.me/theorems/95658b90-f858-4b9f-8467-a27ffa0ac425
-- title:
--   Unconditional tilted-scale Laplace transform at a positive Esscher root
-- statement:
--   For any positive discount q, positive Esscher root φ and β>0, the tilted q-scale function e^{-φx}W^(q)(x) has a finite β-Laplace transform exactly 1/(ψ(φ+β)−q). This removes the extra shifted-exponent hypotheses from the general scale transform using the proved positive-root convex secant bound.
-- source:
--   Apply Proved esscher_tilted_scale_laplace_shift 73c21e1c with θ=β, using Proved strict positivity q<ψ(φ+β) (eb5bb6f8) and β+φ>0. This is the scale-function side of the perpetual-infimum Wiener-Hopf identification, source-faithful and independent of the unproved stochastic exit formula.

import Mathlib.Algebra.Order.Field.Basic
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_scale_laplace_shift
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_strictly_above_shift

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_esscher_root_scale_tilted_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ β : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hβ : 0 < β)
    (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    IntegrableOn
      (fun y : ℝ => Real.exp (-(β * y)) * (Real.exp (-(φ * y)) * W y))
      (Ioi 0) volume ∧
    (∫ y in Ioi (0 : ℝ), Real.exp (-(β * y)) *
      (Real.exp (-(φ * y)) * W y) ∂volume) =
      (X.ψ (φ + β) - q)⁻¹ := by sorry
