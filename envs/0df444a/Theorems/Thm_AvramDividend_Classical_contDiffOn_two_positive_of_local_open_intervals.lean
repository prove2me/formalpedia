-- Prove2me | Theorems.Thm_AvramDividend_Classical_contDiffOn_two_positive_of_local_open_intervals
-- name    : AvramDividend.Classical.contDiffOn_two_positive_of_local_open_intervals
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T11:10:46.647416+00:00
-- url     : https://prove2.me/theorems/2ab8a2be-d49f-4e35-8e6b-cb2f9231c9aa
-- title:
--   Patch local C2 intervals into C2 regularity on the positive half-line
-- statement:
--   If every strictly positive point admits some open real interval on which a function is C2, then the function is C2 on the entire positive half-line. The intervals may shrink toward the origin, accommodating Volterra kernels singular at zero.
-- source:
--   Locality bridge from interval-wise Gaussian resolvent C1 and scale C2 statements to the global positive half-line theorem.

import Mathlib.Analysis.Calculus.ContDiff.Defs

open Set

theorem AvramDividend.Classical.contDiffOn_two_positive_of_local_open_intervals
    (W : ℝ → ℝ)
    (hlocal : ∀ x : ℝ, 0 < x →
      ∃ a b : ℝ, a < x ∧ x < b ∧ ContDiffOn ℝ 2 W (Ioo a b)) :
    ContDiffOn ℝ 2 W (Ioi 0) := by sorry
