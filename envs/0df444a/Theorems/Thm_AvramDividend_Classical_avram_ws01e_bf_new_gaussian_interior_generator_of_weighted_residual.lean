-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_gaussian_interior_generator_of_weighted_residual
-- name    : AvramDividend.Classical.avram_ws01e_bf_new_gaussian_interior_generator_of_weighted_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T01:02:01.414303+00:00
-- url     : https://prove2.me/theorems/704d0791-d853-40f0-9f56-ab9437276208
-- title:
--   Actual Gaussian scale-generator harmonicity from a weighted residual identity family
-- statement:
--   For a genuine Standing Gaussian spectrally negative Levy process and positive real canonical dividend cap, a full family of weighted residual Laplace transform identities is sufficient for the actual scale function to lie in the Levy generator domain and solve (Gamma-q)W=0 throughout the positive interior. The genuine scale C2, origin-zero, full generator-residual continuity and nonzero normaliser are derived rather than separately postulated.
-- source:
--   Source-faithful Gaussian branch of original Open generator_vcstar_eq_zero, reduced to a single explicit all-theta stochastic weighted-transform interface. Composes Proved 4c4d5e79, c1392cb2, 097a29e5, 1fe801dd, 8d7288ac, 19cae668 and 21a2556e. Distinct from existing theorem 21a2556e because it removes its auxiliary C2, continuity, cstar ENNReal positivity and hk premises by deriving them from Standing.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_of_gaussian
import Theorems.Thm_AvramDividend_Classical_gaussian_psi_superlinear_of_positive_sigma
import Theorems.Thm_AvramDividend_Classical_scaleFunction_origin_zero_of_superlinear_psi_nonnegative_q
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_Ioi_of_zero_origin_C2
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_nonzero_at_finite_cstar_of_tilted_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_q_harmonic_of_nonzero_factor_gaussian
open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bf_new_gaussian_interior_generator_of_weighted_residual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) (ha : 0 < (cstar W).toReal)
    (hweighted : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable W x ∧
        X.generator W x - q * W x = 0 := by sorry
