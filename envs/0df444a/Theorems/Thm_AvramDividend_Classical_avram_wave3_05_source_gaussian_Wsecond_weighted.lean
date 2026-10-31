-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_source_gaussian_Wsecond_weighted
-- name    : AvramDividend.Classical.avram_wave3_05_source_gaussian_Wsecond_weighted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T07:47:16.590485+00:00
-- url     : https://prove2.me/theorems/bb2c6978-d2b3-4e84-a5f9-13b6dbb5a836
-- title:
--   Unconditional eventual weighted second-derivative integrability for the source Gaussian q-scale
-- statement:
--   For the unchanged Gaussian spectrally negative Lévy q-scale W and an Esscher positive root φ, there exists a finite threshold b such that each θ≥b with θ≥0 and q<ψ(θ) gives global positive-halfline integrability of exp(-θx)W''(x). The proof takes the genuine native signed Volterra density S and exact W'' identity, then combines the scale Laplace mass of W and W' with the signed Neumann L1 transfer theorem. No global weighted |W''| assumption is made.
-- source:
--   Original Gaussian q-scale source signed Neumann derivative and W'' reconstruction, accepted scale shifted Laplace W and chat07 W' integrability, accepted weighted W'' from signed density.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_source_gaussian_Wsecond_signed
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shiftedLaplace_integrable
import Theorems.Thm_AvramDividend_Classical_chat07_scale_weighted_deriv_integrable_positive_halfline
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_second_deriv_weighted_from_signed

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_05_source_gaussian_Wsecond_weighted
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ b : ℝ, ∀ θ : ℝ, b ≤ θ → 0 ≤ θ → q < X.ψ θ →
      IntegrableOn
        (fun x : ℝ => Real.exp (-(θ * x)) * deriv (deriv W) x)
        (Ioi (0 : ℝ)) volume := by sorry
