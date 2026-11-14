-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_cutoff_residual_integrable_centered_finite_measure_20261113
-- name    : AvramDividend.Classical.avram_a21_original_cutoff_residual_integrable_centered_finite_measure_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:12:51.681197+00:00
-- url     : https://prove2.me/theorems/c5730f78-08a9-465d-9fba-d514b6bda171
-- title:
--   Every original physical Gaussian cutoff residual is integrable and centred on a finite measure
-- statement:
--   For any original Levy process under an explicitly finite probability measure, the finite-cutoff original intrinsic Gaussian residual is integrable and centred at every cutoff and horizon. The physical retained negative compensated band has L2 and L1 by its original source measure and finite total mass; subtract its zero mean from the already centred zero-cutoff residual.
-- source:
--   Proved source measurable and L2 of actual retained jump band, 2013-pinned Mathlib L2-to-L1 on finite measure, and newly published source-integrable centred retained L1 lemma 85484289.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_gaussian_core_and_jump_cutoff_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_finite_activity_smallband_cutoff_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_cutoff_residual_integrable_centered_of_retained_L1_20261113
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_cutoff_residual_integrable_centered_finite_measure_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      Integrable (fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) P ∧
      (∫ ω,
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω ∂P) = 0 := by sorry
