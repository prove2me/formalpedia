-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_gaussian_generator_from_eventual_laplace
-- name    : AvramDividend.Classical.avram_wave3_05_gaussian_generator_from_eventual_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T23:02:19.254984+00:00
-- url     : https://prove2.me/theorems/51e17ccf-d381-43b6-8121-50a198e19d7f
-- title:
--   Gaussian source generator is q-harmonic from residual transforms on a terminal Laplace half-line
-- statement:
--   For the original Standing spectrally negative Levy process with strictly positive Gaussian coefficient and its q-scale function W, if the actual generator residual has an integrable zero weighted Laplace transform at every sufficiently large parameter, then W lies in the generator domain at every positive reserve and (Gamma-q)W vanishes there. This materially weakens the all-admissible-parameter premise of existing Gaussian reductions and permits a large-theta contraction argument. It does not assert that the eventual weighted-integrability premise follows automatically.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 4, and established Laplace uniqueness b4d10133; source-level Gaussian C2 f596d402 and residual continuity 1fe801dd.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_two_of_sigma_pos
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_Ioi_of_zero_origin_C2
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_ae_of_laplace_residual_vanishing
import Theorems.Thm_AvramDividend_Classical_generator_eq_q_on_Ioo_of_ae_zero_and_continuousOn
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_contDiff_two

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_05_gaussian_generator_from_eventual_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hσ : 0 < X.σ)
    (b : ℝ)
    (hweighted : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0) :
    ∀ x : ℝ, 0 < x →
      X.GeneratorIntegrable W x ∧ X.generator W x - q * W x = 0 := by sorry
