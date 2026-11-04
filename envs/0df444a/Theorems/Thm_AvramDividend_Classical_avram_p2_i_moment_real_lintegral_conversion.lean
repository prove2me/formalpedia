-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_real_lintegral_conversion
-- name    : AvramDividend.Classical.avram_p2_i_moment_real_lintegral_conversion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:40:36.12501+00:00
-- url     : https://prove2.me/theorems/0959f66a-0cd6-4df6-b77a-81d1a2db39a2
-- title:
--   Real kth moments equal the toReal of nonnegative ENNReal kth lintegrals
-- statement:
--   For a positive measure on the real line supported almost everywhere on nonnegative z, an integrable kth real monomial has the same real integral as the real conversion of the extended-nonnegative lintegral of (ENNReal.ofReal z)^k. The equality works for finite positive weighted image laws whose support may extend beyond z=1. It is a source-agnostic conversion bridge for P2-B's weighted exponential-image moment identities.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_i_moment_real_lintegral_conversion
    (μ : Measure ℝ) (hpositive : ∀ᵐ z ∂μ, 0 ≤ z)
    (k : ℕ) (hk : Integrable (fun z : ℝ => z ^ k) μ) :
    (∫ z : ℝ, z ^ k ∂μ) =
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ).toReal := by sorry
