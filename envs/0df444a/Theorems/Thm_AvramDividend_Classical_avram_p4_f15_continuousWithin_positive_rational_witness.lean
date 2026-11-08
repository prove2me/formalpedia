-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f15_continuousWithin_positive_rational_witness
-- name    : AvramDividend.Classical.avram_p4_f15_continuousWithin_positive_rational_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:11:05.770694+00:00
-- url     : https://prove2.me/theorems/b76147cf-966e-4936-8c9d-26eedb455b64
-- title:
--   Right-continuous positive nonnegative-real observations have rational witnesses
-- statement:
--   For a real-valued function on nonnegative reals that is continuous from the right at s, if f(s)>0 and s<epsilon, then there is a nonnegative rational time strictly between s and epsilon at which f remains positive. This isolates the topological density and continuity argument required by the original Lévy rational-path equivalence.

import Mathlib
open Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p4_f15_continuousWithin_positive_rational_witness
    (f : ℝ≥0 → ℝ) (s ε : ℝ≥0)
    (hsε : s < ε) (hpos : 0 < f s)
    (hcont : ContinuousWithinAt f (Ici s) s) :
    ∃ q : ℚ≥0, s < (q : ℝ≥0) ∧ (q : ℝ≥0) < ε ∧ 0 < f (q : ℝ≥0) := by sorry
