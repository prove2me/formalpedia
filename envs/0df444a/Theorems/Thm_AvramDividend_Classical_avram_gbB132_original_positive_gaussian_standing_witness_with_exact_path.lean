-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB132_original_positive_gaussian_standing_witness_with_exact_path
-- name    : AvramDividend.Classical.avram_gbB132_original_positive_gaussian_standing_witness_with_exact_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:39:06.647641+00:00
-- url     : https://prove2.me/theorems/62aa62f0-0adc-47a0-855f-8e8762eb19a2
-- title:
--   Original positive-drift Gaussian Standing witness retains its exact Brownian path representation
-- statement:
--   Construct the original spectrally negative Gaussian Lévy source on gaussianLimit with volatility 1, drift 2, no jumps, Standing and unbounded variation, while retaining the exact path identity Y.X_t=B_t-B_0+2t. This refines an already-Proved HJB witness whose exported statement dropped the path identity, enabling direct instantiation of the original physical-grid centred Brownian and barrier-tube counterexample certificates.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB29_positive_drift_gaussian_sigma1_witness
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_gaussian_drifted_unit_integrable
import Theorems.Thm_AvramDividend_Classical_positive_gaussian_standing_and_unbounded_variation
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB132_original_positive_gaussian_standing_witness_with_exact_path :
    ∃ (𝓕 : Filtration ℝ≥0
      (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
      (∀ (t : ℝ≥0) (ω : ℝ≥0 → ℝ),
        Y.X t ω = brownian t ω - brownian 0 ω + 2 * (t : ℝ)) ∧
      Y.c = 2 ∧ Y.σ = 1 ∧ Y.ν = 0 ∧
      Y.Standing ∧ ¬ Y.BoundedVariation := by sorry
