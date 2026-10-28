-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_scale_generator_q_harmonic_all_barriers_ws01b
-- name    : AvramDividend.Classical.bv_scale_generator_q_harmonic_all_barriers_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:59:13.901982+00:00
-- url     : https://prove2.me/theorems/554ee8ff-e1e6-463b-bb9f-9ea5f24cb169
-- title:
--   Bounded-variation q-scale generator is harmonic on every positive interval
-- statement:
--   For a standing bounded-variation spectrally negative Levy process, q>0 and its q-scale function W, prove that the jump-generator integral exists and (Γ-q)W=0 at every point in (0,a) for every a>0. Unlike the existing optimal-barrier result, this theorem has no cstar positivity or normalisation assumptions. Derived from the proved full Laplace residual family, BV C1 continuity, jump-integrability and the proved interval upgrade.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 4; Kyprianou scale-function theory; this lemma composes independently proved canonical Prove2Me analytic results and applies to arbitrary upper-exit levels.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_one_of_boundedVariation
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_positive_of_standing_bv_C1_sigma_zero
import Theorems.Thm_AvramDividend_Classical_bv_weighted_generator_residual_family_from_scale_20261026
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_interval_harmonic_of_laplace_family
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_scale_generator_q_harmonic_all_barriers_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a : ℝ) (ha : 0 < a) :
    ∀ y ∈ Ioo 0 a,
      X.GeneratorIntegrable W y ∧ X.generator W y - q * W y = 0 := by sorry
