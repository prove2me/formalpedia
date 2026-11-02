-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_tail_integrable_upto_one
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_tail_integrable_upto_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:38:36.568127+00:00
-- url     : https://prove2.me/theorems/41a3b4f0-d2d2-4830-afd7-395a0f503a54
-- title:
--   Original bounded-variation Lévy residual has integrable threshold-truncated first moment at small times
-- statement:
--   For the exact original spectrally negative Lévy process satisfying the given Standing and BoundedVariation assumptions, every residual R_t=tX.drift-X_t for t≤1 has an integrable threshold-truncated loss R_t 1_{R_t>M}, for any real threshold M. Apply the already Proved source-process residual integrability theorem and its monotonicity 0≤R_t, prove Borel measurability of the threshold cutoff, and dominate the absolute truncated value by R_t. The result is a genuine expectation-level integrability prerequisite for the BV C1 generator-semigroup bridge; it does not assume jump compensation or any generator limit.
-- source:
--   Private remote-compiler-verified candidate source candidates/work_on/AvramDividend_04c_actual_residual_tail_integrable_probe.lean; not yet proof-submitted.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_integrable_upto_one
set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_tail_integrable_upto_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (t : ℝ≥0) (ht : t ≤ 1) (M : ℝ) :
    Integrable
      (fun ω => if M < (t : ℝ) * X.drift - X.X t ω
        then (t : ℝ) * X.drift - X.X t ω else 0) P := by sorry
