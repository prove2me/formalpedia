-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva19_original_first_cell_discounted_gain_vanishes
-- name    : AvramDividend.Classical.avram_bva19_original_first_cell_discounted_gain_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:43:13.736089+00:00
-- url     : https://prove2.me/theorems/3e722085-7f96-41e8-9d34-2cc9b25dea0b
-- title:
--   Original time-zero right-payment grid cell gain vanishes as the physical grid refines
-- statement:
--   The time-zero term of the original stopped marked compensator grid vanishes on refinement, even when an admissible dividend strategy makes a nonzero right payment at time zero. The left-limit reserve U at zero is a fixed path value and the discount is exactly one; the first physical mesh width tends to zero. This ingredient is needed because the source compensator uses strictly positive times whereas the open grid sums include index zero.
-- source:
--   Original source-exact time-zero atom and first-cell correction in later-ruin compensated Riemann comparison efbae9c3, eventually contributing to b9fee8b9 and 3ae3442d. The general deterministic statement avoids assuming the initial right-payment vanishes.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva19_original_first_cell_discounted_gain_vanishes
    (u : ℕ → ℕ → ℝ≥0) (hzero : ∀ n, u n 0 = 0)
    (hmesh : Tendsto (fun n => (u n 1 : ℝ)) atTop (𝓝 (0 : ℝ)))
    (U : ℝ≥0 → ℝ) (q : ℝ) (ψ : ℝ → ℝ) :
    Tendsto (fun n =>
      Real.exp (-(q * (u n 0 : ℝ))) * ψ (U (u n 0)) *
        ((u n 1 : ℝ) - (u n 0 : ℝ)))
      atTop (𝓝 (0 : ℝ)) := by sorry
