-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB54k_upper_affine_clip_kink_one_sided_cell
-- name    : AvramDividend.Classical.avram_gbB54k_upper_affine_clip_kink_one_sided_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:03:15.053821+00:00
-- url     : https://prove2.me/theorems/d3d9ba81-72ea-45ae-8316-a1c3958e6cc1
-- title:
--   Downward affine upper clipping kink has nonpositive finite-cell first-order excess
-- statement:
--   For any real clipping point b, slope alpha at least one, and any original starting/ending scalar cell values x,y, the piecewise affine potential with slope alpha below b and slope one above b has a nonpositive first-order remainder after linearising at x with its corresponding left-or-right slope. This is the exact finite-step downward-kink sign needed to separate the nonpositive contact contribution in the original finite-cap Gaussian cash source, independent of stochastic assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_gbB54k_upper_affine_clip_kink_one_sided_cell
    (b α x y : ℝ) (hα : 1 ≤ α) :
    let V : ℝ → ℝ := fun z => if z ≤ b then α * z else α * b + (z - b)
    let G : ℝ := if x ≤ b then α else 1
    V y - V x - G * (y - x) ≤ 0 := by sorry
