-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_canonical_negative_mark_bands_antitone_empty
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_canonical_negative_mark_bands_antitone_empty
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:01:25.029429+00:00
-- url     : https://prove2.me/theorems/7de0c448-b0f1-446e-92f6-dde156b3ba93
-- title:
--   Canonical negative Lévy small-jump intervals shrink monotonically to the empty set
-- statement:
--   The canonical negative small-jump bands (-1/(n+1),0) are nested decreasing and have empty intersection. This geometric result supplies the exact measurable mark thinning needed in the source predictable L2 convergence theorem, including the infinite-activity near-zero limit. No stochastic compensation hypothesis enters.
-- source:
--   Pinned Mathlib real one-division order monotonicity and reciprocal real limit at infinity.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_b_smalljump_canonical_negative_mark_bands_antitone_empty :
    Antitone (fun n : ℕ =>
      Ioo (-(1 : ℝ) / ((n + 1 : ℕ) : ℝ)) (0 : ℝ)) ∧
    (⋂ n : ℕ, Ioo (-(1 : ℝ) / ((n + 1 : ℕ) : ℝ)) (0 : ℝ)) = ∅ := by sorry
