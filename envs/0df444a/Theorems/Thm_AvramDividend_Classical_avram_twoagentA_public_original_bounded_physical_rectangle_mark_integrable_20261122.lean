-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_bounded_physical_rectangle_mark_integrable_20261122
-- name    : AvramDividend.Classical.avram_twoagentA_public_original_bounded_physical_rectangle_mark_integrable_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:05:36.687564+00:00
-- url     : https://prove2.me/theorems/9e7b462e-6795-42c2-ae1c-70d1f74e4a43
-- title:
--   Original signed-mark quantizer proof reusable original_bounded_physical_rectangle_mark_integrable_20261122
-- statement:
--   Republish the verbatim remotely accepted private proof as an independently importable PUBLIC original-physical negative-mark finite-band signed integral bridge helper, with the mathematical statement unchanged. The source has no private theorem imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_public_original_bounded_physical_rectangle_mark_integrable_20261122
    (μ : Measure (ℝ≥0 × ℝ)) (T : ℝ≥0) (a b : ℝ)
    (ha : -1 ≤ a) (hb : b ≤ 0)
    (hFin : μ (Ioc (0 : ℝ≥0) T ×ˢ Ioc a b) < ⊤) :
    IntegrableOn (fun p : ℝ≥0 × ℝ => p.2)
      (Ioc (0 : ℝ≥0) T ×ˢ Ioc a b) μ := by sorry
