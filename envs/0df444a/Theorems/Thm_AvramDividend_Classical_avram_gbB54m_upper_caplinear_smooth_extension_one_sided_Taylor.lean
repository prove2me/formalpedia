-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB54m_upper_caplinear_smooth_extension_one_sided_Taylor
-- name    : AvramDividend.Classical.avram_gbB54m_upper_caplinear_smooth_extension_one_sided_Taylor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:17:23.097202+00:00
-- url     : https://prove2.me/theorems/c474aa63-d596-487b-8ffc-f44ca59704de
-- title:
--   Upper caplinear first-order residual bounded by matching smooth-slope extension residual
-- statement:
--   For any function w and upper clipping point b with an interior boundary slope alpha at least one, the one-sided first-order Taylor remainder of the slope-one upper caplinear extension is bounded by the same remainder of the slope-alpha continuation, for any two real cell endpoints x,y and arbitrary interior linearisation gain g. Thus the unfavourable positive contribution of the downward upper kink can be discarded in an original finite-step Gaussian cash-grid inequality without taking an absolute value or assuming away local time.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_gbB54m_upper_caplinear_smooth_extension_one_sided_Taylor
    (w : ℝ → ℝ) (b α g x y : ℝ) (hα : 1 ≤ α) :
    let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
    let U : ℝ → ℝ := fun z => if z ≤ b then w z else w b + α * (z - b)
    let gv : ℝ := if x ≤ b then g else 1
    let gu : ℝ := if x ≤ b then g else α
    V y - V x - gv * (y - x) ≤ U y - U x - gu * (y - x) := by sorry
