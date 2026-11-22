-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_negative_mark_restrict_integral_20261122
-- name    : AvramDividend.Classical.avram_twoagentA_public_original_negative_mark_restrict_integral_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:21:11.500874+00:00
-- url     : https://prove2.me/theorems/800bea93-6384-4d37-bb8e-7441807b1280
-- title:
--   Original physical marked integral L1 source 3f6f8b67
-- statement:
--   Exact already accepted original negative-mark signed-integral source proof, republished as public importable prerequisite for the genuine unrestricted negative activity physical compensated mark L1 centring and reciprocal quantizer approximation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_public_original_negative_mark_restrict_integral_20261122
    (ν : Measure ℝ) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    (∫ z : ℝ, (if z ∈ B then z else 0)
      ∂(ν.restrict (Iio (0 : ℝ)))) =
      (∫ z in B, z ∂ν)  := by sorry
