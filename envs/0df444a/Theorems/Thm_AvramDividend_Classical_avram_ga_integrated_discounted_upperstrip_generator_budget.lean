-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_integrated_discounted_upperstrip_generator_budget
-- name    : AvramDividend.Classical.avram_ga_integrated_discounted_upperstrip_generator_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T12:36:22.692885+00:00
-- url     : https://prove2.me/theorems/00d7661c-29f8-4a25-9b79-129357741056
-- title:
--   Integrate discounted HJB upper-strip generator bound into stopped occupation budget
-- statement:
--   For an integrable discounted generator on a measurable stopped time-set, if its pointwise value is bounded almost everywhere by max(c,0) on the upper strip and by zero otherwise, then its signed integral is bounded above by max(c,0) times upper-strip occupation. This is the time-integration step needed after the original cap-linear HJB inequality.

import Mathlib
open MeasureTheory Set Filter Topology

theorem AvramDividend.Classical.avram_ga_integrated_discounted_upperstrip_generator_budget
    (S : Set ℝ) (q b c : ℝ) (Y G : ℝ → ℝ)
    (hGenI : Integrable (fun t => Real.exp (-(q * t)) * G t)
       (volume.restrict S))
    (hOccI : Integrable (fun t => if b < Y t then (1 : ℝ) else 0)
       (volume.restrict S))
    (hHJB : ∀ᵐ t ∂(volume.restrict S),
       Real.exp (-(q * t)) * G t ≤
         if b < Y t then max c 0 else 0) :
    (∫ t in S, Real.exp (-(q * t)) * G t ∂volume) ≤
      max c 0 * (∫ t in S,
        if b < Y t then (1 : ℝ) else 0 ∂volume) := by sorry
