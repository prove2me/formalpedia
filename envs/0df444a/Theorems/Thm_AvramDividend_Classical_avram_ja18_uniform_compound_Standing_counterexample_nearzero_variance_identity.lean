-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_uniform_compound_Standing_counterexample_nearzero_variance_identity
-- name    : AvramDividend.Classical.avram_ja18_uniform_compound_Standing_counterexample_nearzero_variance_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T16:13:44.994652+00:00
-- url     : https://prove2.me/theorems/0a427c86-360d-4a8e-9e3c-2f22cd8129a8
-- title:
--   Concrete original Standing compound-Poisson counterexample to mis-specified nearzero compensated variance
-- statement:
--   A Prove2Me-constructed genuine original Standing spectrally negative Levy process with diffuse finite negative compound-Poisson marks and Levy measure Lebesgue restricted to (-1,0) satisfies the standing assumptions yet violates the incorrectly stated nearzero-band formula for the intrinsic retained-smallband compensated variance. At cutoff n=0 the actual source is zero, but the proposed RHS is 1/3 at t=1. The obstruction is fully source-backed and does not rely on synthetic processes.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_CP_standing_BV_drift_one_source_exists
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_nearzero_variance_formula_forces_zero_band_energy
import Theorems.Thm_AvramDividend_Classical_avram_ja18_uniform_negative_smallmark_quadratic_energy_one_third
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_uniform_compound_Standing_counterexample_nearzero_variance_identity :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
      (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
      X.Standing ∧ X.ν (Iio (0 : ℝ)) ≠ ⊤ ∧
      ¬ (∀ (n : ℕ) (t : ℝ≥0),
        (∫ ω,
          (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) ^ 2 ∂P) =
          (t : ℝ) *
            (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν)) := by sorry
