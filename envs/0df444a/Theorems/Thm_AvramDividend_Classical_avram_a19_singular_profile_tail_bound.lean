-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_singular_profile_tail_bound
-- name    : AvramDividend.Classical.avram_a19_singular_profile_tail_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:31:05.681915+00:00
-- url     : https://prove2.me/theorems/23283bab-2294-49f0-827b-e0b7b1635999
-- title:
--   Quantitative reciprocal lower-tail bound for the singular HJB profile
-- statement:
--   For 0<t<=1/4, the negative of the explicit scalar HJB profile 3+t^2-4t-2/t is at least 1/t. This supplies the quantitative singular lower-tail estimate needed to show divergence of the proposed original-generator cell counterexample.
-- source:
--   A19 countermodel quantitative path estimate, 7 November 2026.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_a19_singular_profile_tail_bound
    (t : Real) (ht : 0 < t) (htsmall : t <= 1 / 4) :
    1 / t <= -(3 + t ^ 2 - 4 * t - 2 / t) := by sorry
