-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_compact_negative_test_finite_envelope
-- name    : AvramDividend.Classical.avram_p2_j_ui_compact_negative_test_finite_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:20:41.173052+00:00
-- url     : https://prove2.me/theorems/510f2b81-9539-4d60-ae6a-7397e2efa659
-- title:
--   Continuous compactly supported strictly negative tests admit a finite separated ENNReal envelope
-- statement:
--   For a continuous real test whose closed topological support is compact and lies strictly below zero, construct ε>0 and finite ENNReal M such that its e-norm is bounded by M on y≤-ε and vanishes elsewhere. This supplies the exact bounded negative-test hypothesis of the proved original Lévy grid L² and P2-J expectation theorems, without a compensator or pathwise limit.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_compact_negative_support_separation

open MeasureTheory Set Topology AvramDividend.Classical
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_j_ui_compact_negative_test_finite_envelope
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Set.Iio (0 : ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ M : ENNReal, M ≠ ⊤ ∧
      ∀ y : ℝ, ‖g y‖ₑ ≤ if y ≤ -ε then M else 0 := by sorry
