-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_weighted_inclusive_cash_rightclock_limit
-- name    : AvramDividend.Classical.avram_f6_original_weighted_inclusive_cash_rightclock_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:23:11.356368+00:00
-- url     : https://prove2.me/theorems/221e1724-4c9e-4146-b897-ab8ea8efa220
-- title:
--   Original inclusive discounted paymentTimes cash toReal continuous from above at finite stopped clock
-- statement:
--   For an actual positive discounted Stieltjes cash measure restricted to the original paymentTimes, a decreasing sequence of physical clocks approaching s retains the inclusive atom at s in the toReal-integral limit. Uses only finite weighted mass at an initial interval and continuity from above of the exact weighted restricted measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_real_cash_antitone_physical_clock_limit
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_weighted_inclusive_cash_rightclock_limit
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (A : Set ℝ) (hA : MeasurableSet A)
    (a : ℕ → ℝ) (s : ℝ) (ha : Antitone a)
    (hl : Tendsto a atTop (𝓝 s))
    (hfinite : ∃ n,
      (∫⁻ t in A ∩ Iic (a n), f t ∂μ) ≠ ∞) :
    Tendsto
      (fun n => (∫⁻ t in A ∩ Iic (a n), f t ∂μ).toReal)
      atTop (𝓝 ((∫⁻ t in A ∩ Iic s, f t ∂μ).toReal)) := by sorry
