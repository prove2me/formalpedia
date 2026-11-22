-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_finiteband_clock_compensator_identity_20261122
-- name    : AvramDividend.Classical.avram_twoagentA_public_original_finiteband_clock_compensator_identity_20261122
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T14:31:56.377975+00:00
-- url     : https://prove2.me/theorems/21492682-7627-468c-851e-192f2a7b4c86
-- title:
--   Original finiteband physical compensated signed mark source chain 2
-- statement:
--   Republish exact previously accepted actual original compensated negative marked physical finite-horizon time clock integral, masked stopping rectangle and Campbell-mark centring, using exclusively public proved source-faithful original-X dependencies.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_negative_mark_restrict_integral_20261122
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_positive_clock_integral_indicator_const_20261122
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_public_original_finiteband_clock_compensator_identity_20261122
    (T : ℝ≥0) (ν : Measure ℝ) (B : Set ℝ)
    (hBm : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (hBI : IntegrableOn (fun z : ℝ => z) B ν) :
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
    (∫ t : ℝ≥0, ∫ z : ℝ,
      (if t ∈ Ioc 0 T ∧ z ∈ B then z else 0)
        ∂(ν.restrict (Iio (0 : ℝ))) ∂μT) =
      (T : ℝ) * (∫ z in B, z ∂ν) := by sorry
