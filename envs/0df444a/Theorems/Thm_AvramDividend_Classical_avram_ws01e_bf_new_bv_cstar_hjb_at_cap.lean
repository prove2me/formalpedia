-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_bv_cstar_hjb_at_cap
-- name    : AvramDividend.Classical.avram_ws01e_bf_new_bv_cstar_hjb_at_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:23:16.931042+00:00
-- url     : https://prove2.me/theorems/114941db-8e11-4758-bad5-4332c72ab331
-- title:
--   Unconditional positive bounded-variation optimal dividend HJB at the exact barrier
-- statement:
--   For any Standing bounded-variation spectrally negative Levy process with positive discount and genuine q-scale function, whenever the real optimal barrier is positive, the exact dividend-value candidate is generator-integrable at the barrier, has zero discounted generator residual there, and satisfies the complete HJB maximum equality at that boundary. The positive derivative of W follows from its genuine Esscher tilt and strict positivity, BV C1 gives generator-domain integrability, the Proved actual BV interior scale harmonicity and continuous generator residual extend to the cap by a Proved cap-transfer theorem, and an accepted genuine smooth-fit theorem supplies unit derivative. No above-barrier generator inequality is required.
-- source:
--   Source-faithful bounded-variation barrier-point constituent of AvramDividend.Classical.vcstar_hjb_at_positive_cstar (8d03da6b) and vcstar_hjb_all_positive_of_generator (edf09308), from accepted Standing BV C1 continuity bae40e79, actual q-scale harmonicity 554ee8ff, cap-transfer 073b643f, Esscher positivity 8d7288ac and genuine BV smooth fit a670aadb. This removes the prior C2 and weighted-Laplace premises of the accepted conditional cap theorems 3c02ea3c and 328de415.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_one_of_boundedVariation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_bv
import Theorems.Thm_AvramDividend_Classical_normalized_derivative_lower_bound
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_positive_of_standing_bv_C1_sigma_zero
import Theorems.Thm_AvramDividend_Classical_bv_scale_generator_q_harmonic_all_barriers_ws01b
import Theorems.Thm_AvramDividend_Classical_chat07_vcstar_pure_jump_cap_harmonic_of_differentiable_scale
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top_of_bv_standing
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_bv_smoothfit_of_standing
open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bf_new_bv_cstar_hjb_at_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation)
    (ha : 0 < (cstar W).toReal) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal = 0 ∧
      max (X.generator (vcstar W) (cstar W).toReal -
          q * vcstar W (cstar W).toReal)
          (1 - deriv (vcstar W) (cstar W).toReal) = 0 := by sorry
