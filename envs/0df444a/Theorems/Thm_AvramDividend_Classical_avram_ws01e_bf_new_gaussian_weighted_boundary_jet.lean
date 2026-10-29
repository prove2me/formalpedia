-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_gaussian_weighted_boundary_jet
-- name    : AvramDividend.Classical.avram_ws01e_bf_new_gaussian_weighted_boundary_jet
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:39:50.425818+00:00
-- url     : https://prove2.me/theorems/8d284440-c9da-4cd6-a401-89348e4169be
-- title:
--   Actual Gaussian weighted boundary jet at the finite positive optimal dividend barrier
-- statement:
--   For a Standing spectrally negative Levy process with positive Gaussian coefficient, positive discount and actual q-scale function, at every strictly positive real cstar the candidate dividend value agrees with its normalized scale branch below cstar and has matching first derivative and Gaussian-weighted second derivative at cstar. Genuine Gaussian C2 regularity and Esscher positivity supply differentiability and a nonzero scale derivative. The positive canonical barrier minimizes W', so W''=0; the already Proved first- and second-order smooth-fit calculus glue the branches. No extra regularity or stationary derivative hypothesis is added.
-- source:
--   Source-faithful Gaussian constituent of AvramDividend.Classical.vcstar_scaledW_matched_weighted_jet_at_cstar (22df0d92). Uses Proved actual Gaussian scale C2 4c4d5e79, positive Esscher tilt 8d7288ac, canonical second derivative stationarity 40dc3aef, and generic first/second matching 2e8cdfd8. Combined with our BV branch ef8bd2b6 it supports canonical cap-generator harmonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_normalized_derivative_lower_bound
import Theorems.Thm_AvramDividend_Classical_deriv_deriv_eq_zero_at_positive_cstar_of_deriv_continuous
import Theorems.Thm_AvramDividend_Classical_vcstar_first_deriv_smooth_fit_of_nonzero
import Theorems.Thm_AvramDividend_Classical_vcstar_second_deriv_smooth_fit_of_stationary_scale_deriv
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_scaledW_le_cstar_of_support
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_at_positive_cstar
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_gaussian_cstar_lt_top
open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bf_new_gaussian_weighted_boundary_jet
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (ha : 0 < (cstar W).toReal) :
    (∀ z : ℝ, z ≤ (cstar W).toReal →
      vcstar W z = (fun z : ℝ =>
        divE (W z) (scaleDeriv W (cstar W).toReal)) z) ∧
    deriv (vcstar W) (cstar W).toReal =
      deriv (fun z : ℝ =>
        divE (W z) (scaleDeriv W (cstar W).toReal)) (cstar W).toReal ∧
    X.σ ^ 2 * iteratedDeriv 2 (vcstar W) (cstar W).toReal =
      X.σ ^ 2 * iteratedDeriv 2 (fun z : ℝ =>
        divE (W z) (scaleDeriv W (cstar W).toReal)) (cstar W).toReal := by sorry
