-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_physical_signed_mark_constant_shift_integral_20261122
-- name    : AvramDividend.Classical.avram_twoagentA_public_original_physical_signed_mark_constant_shift_integral_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:05:23.948133+00:00
-- url     : https://prove2.me/theorems/8183a176-a7a0-4241-b675-9008896abd77
-- title:
--   Original signed-mark quantizer proof reusable original_physical_signed_mark_constant_shift_integral_20261122
-- statement:
--   Republish the verbatim remotely accepted private proof as an independently importable PUBLIC original-physical negative-mark finite-band signed integral bridge helper, with the mathematical statement unchanged. The source has no private theorem imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_public_original_physical_signed_mark_constant_shift_integral_20261122
    (μ : Measure (ℝ≥0 × ℝ)) (S : Set (ℝ≥0 × ℝ)) (c : ℝ)
    (hFin : μ S < ⊤)
    (hInt : IntegrableOn (fun p : ℝ≥0 × ℝ => p.2) S μ) :
    (∫ p in S, p.2 + c ∂μ) =
      (∫ p in S, p.2 ∂μ) + c * (μ S).toReal := by sorry
