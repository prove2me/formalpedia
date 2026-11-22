-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_time_mark_negative_bin_integral_error_20261122
-- name    : AvramDividend.Classical.avram_twoagentA_public_original_time_mark_negative_bin_integral_error_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:05:25.736692+00:00
-- url     : https://prove2.me/theorems/16df65be-766e-47b6-acc9-496f9431102c
-- title:
--   Original signed-mark quantizer proof reusable original_time_mark_negative_bin_integral_error_20261122
-- statement:
--   Republish the verbatim remotely accepted private proof as an independently importable PUBLIC original-physical negative-mark finite-band signed integral bridge helper, with the mathematical statement unchanged. The source has no private theorem imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_public_original_time_mark_negative_bin_integral_error_20261122
    (μ : Measure (ℝ≥0 × ℝ)) (T : ℝ≥0) (i : ℕ)
    (hFin : μ (Ioc (0 : ℝ≥0) T ×ˢ
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))) < ⊤) :
    |∫ p in Ioc (0 : ℝ≥0) T ×ˢ
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2))),
      p.2 + 1 / ((i : ℝ) + 1) ∂μ| ≤
    (1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))) *
      μ.real (Ioc (0 : ℝ≥0) T ×ˢ
        Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))) := by sorry
