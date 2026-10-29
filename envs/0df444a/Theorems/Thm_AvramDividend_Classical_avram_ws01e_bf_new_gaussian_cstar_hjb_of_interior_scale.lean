-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_gaussian_cstar_hjb_of_interior_scale
-- name    : AvramDividend.Classical.avram_ws01e_bf_new_gaussian_cstar_hjb_of_interior_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:53:26.739718+00:00
-- url     : https://prove2.me/theorems/dde2de32-f556-44be-8991-7b3631b6fa83
-- title:
--   Actual Gaussian cap HJB from only interior scale q-harmonicity
-- statement:
--   For an actual Standing Gaussian spectrally negative Levy process with q>0 and positive real canonical barrier, assume only the genuine missing interior scale-generator q-harmonicity equation. Then at cstar the actual dividend candidate belongs to the nonlocal generator domain and has zero discounted residual and exactly zero HJB maximum. No further origin, C2, derivative or generator-integrability hypothesis is assumed: Gaussian C2 and superlinear exponent give W(0)=0 and local domain/continuity, accepted Gaussian boundary jet gives first and second matching, and accepted Gaussian smooth fit gives derivative one.
-- source:
--   Conditional but source-faithful Gaussian constituent of canonical vcstar_hjb_at_positive_cstar (8d03da6b). It explicitly isolates the stochastic generator q-harmonicity still missing without imposing it on the canonical target. Uses already Proved analytic Gaussian C2, origin-zero, generator-domain and continuity, and separately submitted Gaussian weighted jet 8d284440 after it is remotely Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_of_gaussian
import Theorems.Thm_AvramDividend_Classical_gaussian_psi_superlinear_of_positive_sigma
import Theorems.Thm_AvramDividend_Classical_scaleFunction_origin_zero_of_superlinear_psi_nonnegative_q
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_contDiff_two
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_Ioi_of_zero_origin_C2
import Theorems.Thm_AvramDividend_Classical_chat07_vcstar_cap_harmonic_of_continuity_and_matched_jets
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_gaussian_weighted_boundary_jet
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_gaussian_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_at_positive_cstar
open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bf_new_gaussian_cstar_hjb_of_interior_scale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) (ha : 0 < (cstar W).toReal)
    (hinside : ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.generator W x - q * W x = 0) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal = 0 ∧
      max (X.generator (vcstar W) (cstar W).toReal -
          q * vcstar W (cstar W).toReal)
          (1 - deriv (vcstar W) (cstar W).toReal) = 0 := by sorry
