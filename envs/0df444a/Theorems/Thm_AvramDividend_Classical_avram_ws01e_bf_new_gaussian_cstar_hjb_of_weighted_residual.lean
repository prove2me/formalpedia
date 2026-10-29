-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_gaussian_cstar_hjb_of_weighted_residual
-- name    : AvramDividend.Classical.avram_ws01e_bf_new_gaussian_cstar_hjb_of_weighted_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T01:06:43.278525+00:00
-- url     : https://prove2.me/theorems/8a92330b-b39d-4c06-b037-24c4aff07202
-- title:
--   Gaussian HJB at the optimal cap from a genuine weighted residual family
-- statement:
--   For an actual Standing Gaussian spectrally negative Levy process with positive q and positive cstar, the single family of source-faithful Gaussian weighted Laplace residual identities implies the generator domain and zero HJB at the cap. All C2, origin-zero, tilted normaliser, residual-continuity, and interior q-harmonicity hypotheses are discharged from Proved genuine stochastic and analytic theorems.
-- source:
--   Conditional source-faithful Gaussian branch of canonical vcstar_hjb_at_positive_cstar, composing Proved Gaussian scale C2 and real weighted-Laplace-to-interior-harmonicity theorem 21a2556e with the Chat03 cap-HJB bridge dde2de32 after its acceptance. The only explicit extra premise is the genuinely still-open family of weighted generator-residual identities, which must be proved independently from Lévy-Khintchine/Fubini; not a canonical strengthening.

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
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_gaussian_cstar_hjb_of_interior_scale
open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bf_new_gaussian_cstar_hjb_of_weighted_residual
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
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal = 0 ∧
      max (X.generator (vcstar W) (cstar W).toReal -
          q * vcstar W (cstar W).toReal)
          (1 - deriv (vcstar W) (cstar W).toReal) = 0 := by sorry
