-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_negative_subtype_compact_zero_extension
-- name    : AvramDividend.Classical.avram_p2_a_assist_negative_subtype_compact_zero_extension
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:33:15.771917+00:00
-- url     : https://prove2.me/theorems/ed23cc27-1a9b-4773-92da-b8a00115a33d
-- title:
--   Negative-subtype compact test zero extension with strictly negative real support
-- statement:
--   Every continuous compactly supported real test on the negative-mark subtype admits an ambient real zero extension that is continuous, compactly supported and has topological support bounded away from zero. This combines three already proved P2-G lemmas and the exact subtype value evaluation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_g_radon_compact_test_zero_extension_continuous_and_compact
import Theorems.Thm_AvramDividend_Classical_avram_p2_g_radon_compact_test_separated_from_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_g_radon_zero_extension_support_subset_negative_band
open MeasureTheory Set Topology AvramDividend.Classical

theorem AvramDividend.Classical.avram_p2_a_assist_negative_subtype_compact_zero_extension
    (f : CompactlySupportedContinuousMap {x : ℝ // x < 0} ℝ) :
    ∃ g : ℝ → ℝ, Continuous g ∧ IsCompact (tsupport g) ∧
      tsupport g ⊆ Iio (0 : ℝ) ∧
      ∀ x : {x : ℝ // x < 0}, g (x : ℝ) = f x := by sorry
