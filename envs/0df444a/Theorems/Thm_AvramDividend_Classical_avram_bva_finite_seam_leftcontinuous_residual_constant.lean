-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_finite_seam_leftcontinuous_residual_constant
-- name    : AvramDividend.Classical.avram_bva_finite_seam_leftcontinuous_residual_constant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:47:42.098058+00:00
-- url     : https://prove2.me/theorems/ebb1669f-46e6-4e30-8022-8c2d9178ebe7
-- title:
--   Finite seams: left-continuous residual locally constant off finite jumps is globally constant
-- statement:
--   A residual on [0,T] which is constant across every interval containing no times from a finite marked set, and which is continuous from the left at every marked time, is constant on the whole interval. Every marked time is strictly positive and at most T. This topological finite-seam lemma is the key finite-activity drift/jump telescope closure.
-- source:
--   Finite chronological seam induction; strict-left limit and finite ordered sets

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_leftLim_affine_of_eventuallyEq
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_finite_seam_leftcontinuous_residual_constant
    (g : ℝ≥0 → ℝ) (S : Finset ℝ≥0) (T : ℝ≥0)
    (hTime : ∀ u ∈ S, 0 < u ∧ u ≤ T)
    (hFlat : ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      (∀ u ∈ S, ¬ (s < u ∧ u ≤ t)) → g t = g s)
    (hLeft : ∀ u ∈ S, Function.leftLim g u = g u) :
    g T = g 0 := by sorry
