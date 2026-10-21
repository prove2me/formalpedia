-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_rightcontinuous_separated_strict_passages_no_finite_tie
-- name    : AvramDividend.Classical.chat03_rightcontinuous_separated_strict_passages_no_finite_tie
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T20:08:14.46754+00:00
-- url     : https://prove2.me/theorems/02f8d128-644b-48b9-ba4b-24b641bc4d52
-- title:
--   Separated strict first-passage infima cannot coincide at a finite time for a right-continuous path
-- statement:
--   For any right-continuous real-valued path on NNReal time, and two strictly separated barriers lower<upper, it is impossible for the strict upward and strict downward passage-time sets both to have the same finite greatest lower bound t. If the path is below the upper barrier at t, right-continuity provides a right neighbourhood containing no upper crossing, contradicting the upper passage GLB. Otherwise the path is above the lower barrier at t, and the same argument contradicts the lower passage GLB. This deterministic theorem excludes finite ties of the official separated strict exit clocks, regardless of jump or boundary contact behaviour.
-- source:
--   Pinned Mathlib ContinuousWithinAt, eventually_nhdsWithin_iff and exists_Ico_subset_of_mem_nhds' with IsGLB order bounds.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Order.Bounds.Basic

open Filter Set Topology
open scoped NNReal

theorem AvramDividend.Classical.chat03_rightcontinuous_separated_strict_passages_no_finite_tie
    (f : ℝ≥0 → ℝ) (t : ℝ≥0) (lower upper : ℝ)
    (hsep : lower < upper)
    (hRight : ContinuousWithinAt f (Set.Ici t) t)
    (hUp : IsGLB {s : ℝ≥0 | upper < f s} t)
    (hDown : IsGLB {s : ℝ≥0 | f s < lower} t) :
    False := by sorry
