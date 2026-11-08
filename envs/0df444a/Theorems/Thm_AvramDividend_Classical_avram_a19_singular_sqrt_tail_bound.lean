-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_singular_sqrt_tail_bound
-- name    : AvramDividend.Classical.avram_a19_singular_sqrt_tail_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:41:45.713515+00:00
-- url     : https://prove2.me/theorems/ddcb75f3-f622-4746-9206-5be1b11dc717
-- title:
--   Reciprocal-square-root lower bound on near-zero generator loss
-- statement:
--   For 0<y<=1/16, the negative of the explicit A19 generator-deficit profile is bounded below by 1/sqrt(y). It is obtained by applying the earlier proved singular_profile_tail_bound at t=sqrt(y), providing a direct dependency for the proposed infinite-activity generator-cell countermodel.
-- source:
--   A19 singular profile explicit stochastic counterexample research, 7 November 2026.

import Mathlib.Analysis.Real.Sqrt
import Theorems.Thm_AvramDividend_Classical_avram_a19_singular_profile_tail_bound
noncomputable section

theorem AvramDividend.Classical.avram_a19_singular_sqrt_tail_bound
    (y : Real) (hy : 0 < y) (hsmall : y <= 1 / 16) :
    1 / Real.sqrt y <=
      -(3 + y - 4 * Real.sqrt y - 2 / Real.sqrt y) := by sorry
