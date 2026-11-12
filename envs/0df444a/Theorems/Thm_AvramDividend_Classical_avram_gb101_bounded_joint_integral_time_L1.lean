-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb101_bounded_joint_integral_time_L1
-- name    : AvramDividend.Classical.avram_gb101_bounded_joint_integral_time_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:22:47.1742+00:00
-- url     : https://prove2.me/theorems/411a36b0-4e25-4bdc-bc9a-512e04f7acff
-- title:
--   Finite-horizon integrability of expected bounded jointly measurable random fields
-- statement:
--   A bounded jointly measurable real random field with integrable fibres has an expected value integrable on a finite deterministic time interval.
-- source:
--   Time-integration analytic child needed for the original Gaussian gb97.

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_gb101_bounded_joint_integral_time_L1
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (T : ℝ) (f : ℝ → Ω → ℝ)
    (hf : StronglyMeasurable (fun z : ℝ × Ω => f z.1 z.2))
    (hInt : ∀ t, Integrable (f t) P)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ t ω, ‖f t ω‖ ≤ B) :
    IntegrableOn (fun t => ∫ ω, f t ω ∂P)
      (Ioo (0 : ℝ) T) volume := by sorry
