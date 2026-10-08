-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuous_measureReal_Iic_of_finite_noAtoms
-- name    : AvramDividend.Classical.continuous_measureReal_Iic_of_finite_noAtoms
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T13:30:37.039931+00:00
-- url     : https://prove2.me/theorems/2e775541-1d6a-4fc2-a38b-d0f4098a969e
-- title:
--   Atomless locally finite lower cumulative mass is continuous
-- statement:
--   If a measure on the real line has no singleton atoms and every lower interval (-∞,x] has finite mass, then its real-valued cumulative mass x↦μ((-∞,x]) is continuous. This is the deterministic measure-theory step underlying continuity of atomless excursion-height or renewal cumulative functions. A direct Mathlib proof integrates the constant function 1 over lower intervals and uses the pinned primitive-continuity theorem.
-- source:
--   Pinned Mathlib MeasureTheory.IntegrableOn.continuousOn_Iic_primitive_Iic and setIntegral_one_eq_measureReal; source-neutral helper for Avram scale-function regularity.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.continuous_measureReal_Iic_of_finite_noAtoms
    (μ : Measure ℝ) [NullSingletonClass μ]
    (hfin : ∀ x : ℝ, μ (Iic x) ≠ ⊤) :
    Continuous (fun x : ℝ => μ.real (Iic x)) := by sorry
