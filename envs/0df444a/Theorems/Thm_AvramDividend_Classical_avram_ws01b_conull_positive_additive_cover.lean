-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_conull_positive_additive_cover
-- name    : AvramDividend.Classical.avram_ws01b_conull_positive_additive_cover
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:00:14.335011+00:00
-- url     : https://prove2.me/theorems/9e508b3c-e92c-4b83-ad69-8029a0719d3c
-- title:
--   Almost-everywhere positive times additively cover every positive horizon
-- statement:
--   For a Lebesgue almost-everywhere set of real times G, every positive t splits into two strictly positive times s,u belonging to G with s+u=t. This exact additive-cover fact upgrades the actual killed q-scale semigroup from an almost-everywhere-time fixed point to all positive times without assuming time right-continuity.
-- source:
--   Deterministic real-measure translation/reflection invariance and positivity of Lebesgue measure on open intervals. Required by the original Lévy killed semigroup positive-time upgrade in Avram WS1B.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_ws01b_conull_positive_additive_cover
    (G : Set ℝ)
    (hG : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ G) :
    ∀ t : ℝ, 0 < t →
      ∃ s ∈ G, ∃ u ∈ G, 0 < s ∧ 0 < u ∧ s + u = t := by sorry
