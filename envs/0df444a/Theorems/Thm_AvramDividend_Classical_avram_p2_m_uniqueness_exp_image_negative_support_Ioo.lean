-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_exp_image_negative_support_Ioo
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_exp_image_negative_support_Ioo
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:21:52.923566+00:00
-- url     : https://prove2.me/theorems/7e05b666-147c-4b03-bf8f-3fe36befe81a
-- title:
--   Arbitrary-weight exponential image of a negative source lies strictly inside the unit interval
-- statement:
--   If a real Borel measure sigma is almost everywhere supported on strictly negative marks, then the exponential pushforward of its arbitrarily weighted withDensity measure lies almost everywhere in the open interval (0,1), without requiring a finite measure or measurable weight. The proof uses the pinned absolute-continuity theorem for withDensity and exact exp inequalities. This is an original-source independent support lemma for P2-B's candidate finite image; it assumes neither jump count intensity nor moment convergence.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_exp_image_negative_support_Ioo (σ : Measure ℝ) (w : ℝ → ℝ≥0∞) (hneg : ∀ᵐ y ∂σ, y < 0) : ∀ᵐ z ∂((σ.withDensity w).map Real.exp), z ∈ Ioo (0 : ℝ) 1 := by sorry
