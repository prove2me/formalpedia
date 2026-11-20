-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_closed_cash_antitone_clock_limit
-- name    : AvramDividend.Classical.avram_f6_original_closed_cash_antitone_clock_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T15:59:04.072195+00:00
-- url     : https://prove2.me/theorems/e6ff6089-9039-47ee-bcb1-b5042a1c44e6
-- title:
--   Original inclusive closed dividend cash measure is continuous under decreasing physical clocks
-- statement:
--   For a genuine measure on real payment time, the inclusive Iic cash mass at any decreasing sequence of real clock endpoints tending to s converges to the inclusive mass at s, provided some initial mass is finite. Preserves atom at s; supplies deterministic continuity from above required for original dividendMeasure ruincontact.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_closed_cash_antitone_clock_limit
    (μ : Measure ℝ) (a : ℕ → ℝ) (s : ℝ)
    (ha : Antitone a)
    (hl : Tendsto a atTop (𝓝 s))
    (hfinite : ∃ n, μ (Iic (a n)) ≠ ∞) :
    Tendsto (fun n => μ (Iic (a n))) atTop
      (𝓝 (μ (Iic s))) := by sorry
