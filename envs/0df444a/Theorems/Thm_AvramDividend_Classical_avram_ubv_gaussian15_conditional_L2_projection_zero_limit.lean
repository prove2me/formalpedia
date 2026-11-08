-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian15_conditional_L2_projection_zero_limit
-- name    : AvramDividend.Classical.avram_ubv_gaussian15_conditional_L2_projection_zero_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:39:54.830579+00:00
-- url     : https://prove2.me/theorems/009ebfa5-3325-4d71-b2b6-21f0d93c3fd4
-- title:
--   Conditional expectation remains zero for an L2 terminal limit of centred Gaussian grids
-- statement:
--   For any explicitly chosen original sub-sigma-algebra of the same probability space, if original Gaussian finite-grid gains represented as L2 elements have zero conditional expectation and converge in L2, their actual terminal L2 limit has zero conditional expectation with respect to that unchanged sub-sigma-algebra. This supplies the martingale conditional-centering passage after source grid construction.
-- source:
--   Mathlib pinned condExpL2 is a continuous linear orthogonal projection; continuity of its application and uniqueness of a limit give the theorem.

import Mathlib

open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian15_conditional_L2_projection_zero_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (𝓖 : MeasurableSpace Ω) (h𝓖 : 𝓖 ≤ mΩ)
    (Q : ℕ → Lp ℝ 2 P) (L : Lp ℝ 2 P)
    (hZero : ∀ n, (condExpL2 ℝ ℝ h𝓖) (Q n) = 0)
    (hConv : Tendsto Q atTop (𝓝 L)) :
    (condExpL2 ℝ ℝ h𝓖) L = 0 := by sorry
