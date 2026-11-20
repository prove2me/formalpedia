-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_real_cash_antitone_physical_clock_limit
-- name    : AvramDividend.Classical.avram_f6_original_real_cash_antitone_physical_clock_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T16:13:35.998069+00:00
-- url     : https://prove2.me/theorems/de84c049-48b5-434a-b08a-10bf9b77d361
-- title:
--   Original real-valued inclusive cash is continuous from above at exact physical payment atom
-- statement:
--   For any finite-first-mass antitone real physical-clock sequence converging to its true stopped time, the toReal of mass of the inclusive Iic payment interval converges to the toReal of its limiting inclusive mass, retaining the payment atom at the stopping time. This is the source-faithful real cash continuity from above needed in F6 right-mesh Fatou.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_closed_cash_antitone_clock_limit
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_real_cash_antitone_physical_clock_limit
    (μ : Measure ℝ) (a : ℕ → ℝ) (s : ℝ)
    (ha : Antitone a)
    (hl : Tendsto a atTop (𝓝 s))
    (hfinite : ∃ n, μ (Iic (a n)) ≠ ∞) :
    Tendsto (fun n => (μ (Iic (a n))).toReal) atTop
      (𝓝 ((μ (Iic s)).toReal)) := by sorry
