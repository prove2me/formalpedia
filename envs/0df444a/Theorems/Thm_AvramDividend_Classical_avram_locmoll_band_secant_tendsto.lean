-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_secant_tendsto
-- name    : AvramDividend.Classical.avram_locmoll_band_secant_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:40:33.281143+00:00
-- url     : https://prove2.me/theorems/a16b6167-2249-5f5e-b319-670d3f5f26c0
-- title:
--   Extended secants converge when both ordered endpoints converge, including the diagonal
-- statement:
--   Extended secants converge when both ordered endpoints converge, including the diagonal
-- source:
--   Physical Stieltjes integral route to 8b646752-f25d-4029-9771-dda1d287c7e1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_band_secant_tendsto
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (a b : ℕ → ℝ) (A B : ℝ)
    (hab : ∀ n, b n ≤ a n) (hAB : B ≤ A)
    (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B)) :
    let Q : ℝ → ℝ → ℝ := fun a b => if a = b then deriv g a else (g a - g b) / (a - b)
    Tendsto (fun n => Q (a n) (b n)) atTop (𝓝 (Q A B)) := by sorry
