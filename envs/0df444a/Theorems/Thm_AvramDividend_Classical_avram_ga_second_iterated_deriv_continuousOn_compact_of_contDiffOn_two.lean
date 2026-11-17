-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_second_iterated_deriv_continuousOn_compact_of_contDiffOn_two
-- name    : AvramDividend.Classical.avram_ga_second_iterated_deriv_continuousOn_compact_of_contDiffOn_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T17:46:24.583892+00:00
-- url     : https://prove2.me/theorems/99c1610c-a7c4-490d-a531-368c99abef50
-- title:
--   C2 regularity yields continuous second derivative on any compact interior band
-- statement:
--   If w is twice continuously differentiable on an open subset U of the real line, its second classical iterated derivative is continuous on any closed interval included in U. This supplies the deterministic compact-band bound for the finite-cap Gaussian physical-grid Hessian coefficient.

import Mathlib
open Set Topology Filter MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ga_second_iterated_deriv_continuousOn_compact_of_contDiffOn_two
    (w : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hw : ContDiffOn ℝ 2 w U)
    (a b : ℝ) (hsub : Icc a b ⊆ U) :
    ContinuousOn (fun y => iteratedDeriv 2 w y) (Icc a b) := by sorry
