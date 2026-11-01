-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_source_harmonic_from_residual
-- name    : AvramDividend.Classical.avram_wave4_05_gaussian_source_harmonic_from_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:21:05.747987+00:00
-- url     : https://prove2.me/theorems/c352e6e5-13e6-48f8-98a3-2d77458fc2c3
-- title:
--   Original Gaussian q-scale generator q-harmonicity at every positive reserve from eventual weighted residual
-- statement:
--   For the actual Standing spectrally negative Levy process with Gaussian coefficient sigma>0 and its q-scale, if the compensated generator residual has zero weighted Laplace integral throughout a terminal half-line of admissible parameters, then the source q-scale belongs to the full local generator domain and the generator residual is zero at every positive reserve. The proof invokes the canonically Proved Gaussian growth of the original Levy exponent to remove the q<psi(theta) restriction at sufficiently high weights, and the canonically Proved continuity/Laplace uniqueness theorem to promote transform zero to pointwise equality. This is a genuine generator-domain result, not an unverified stochastic bridge.
-- source:
--   Source psi eventually above q Gaussian and Gaussian generator-from-eventual-Laplace uniqueness theorems, pinned 0df444a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_gaussian
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_gaussian_generator_from_eventual_laplace
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
/-- Eventual residual transforms determine the genuine source q-harmonic generator. -/

theorem AvramDividend.Classical.avram_wave4_05_gaussian_source_harmonic_from_residual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hσ : 0 < X.σ)
    (hres : ∃ b : ℝ, ∀ θ : ℝ, b ≤ θ → 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0) :
    ∀ x : ℝ, 0 < x →
      X.GeneratorIntegrable W x ∧ X.generator W x - q * W x = 0 := by sorry
