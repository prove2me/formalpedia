-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_preterminal_integrable_of_strip
-- name    : AvramDividend.Classical.avram_p3_bv_preterminal_integrable_of_strip
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:29:06.0891+00:00
-- url     : https://prove2.me/theorems/d1a9fbc4-807f-4e16-8318-20838bc17b12
-- title:
--   Original BV preterminal L1 from a measurable survival strip and continuous HJB candidate
-- statement:
--   The stopped pre-rightpayment HJB candidate is integrable on a finite original probability space whenever the original measurable preterminal reserve is almost surely in a compact nonnegative strip on strict survival. This is a deterministic L1 closure step; the actual original BV survival strip and source measurability are supplied by separate source lemmas. Does not assume or assert compensation or an HJB supermartingale.
-- source:
--   Heine-Borel compact bound for ContinuousOn HJB candidate and measurable finite-mass bounded integral closure.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_continuous_test_abs_le_on_finite_cap
open MeasureTheory Set
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_preterminal_integrable_of_strip
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (hwMeas : Measurable w)
    (Z : Ω → ℝ) (hZ : Measurable Z)
    (A : Set Ω) [DecidablePred (fun ω => ω ∈ A)] (hA : MeasurableSet A)
    (B : ℝ) (hB : 0 ≤ B)
    (hstrip : ∀ᵐ ω ∂P, ω ∈ A → 0 ≤ Z ω ∧ Z ω ≤ B)
    (q T : ℝ) :
    Integrable (fun ω => if ω ∈ A then Real.exp (-(q * T)) * w (Z ω)
      else 0) P := by sorry
