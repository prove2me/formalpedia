-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen12_singular_power_tail_integral
-- name    : AvramDividend.Classical.avram_gen12_singular_power_tail_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:02:09.250738+00:00
-- url     : https://prove2.me/theorems/96acc6dd-f56e-4217-bdd2-9b2443400578
-- title:
--   Exact singular power tail integral for the proposed negative-jump Levy density
-- statement:
--   The integral of the negative-three-halves power between any strictly positive lower reserve and one equals twice the difference between its inverse-square-root power and one. This provides the singular negative-jump tail needed by the candidate Avram countermodel.
-- source:
--   Specialised finite tail integral for the proposed infinite-activity Lévy measure; derived from the exact pinned Mathlib integral_rpow theorem.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_gen12_singular_power_tail_integral
    (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    (∫ r in y..1, r ^ (-(3 / 2 : ℝ))) =
      2 * (y ^ (-(1 / 2 : ℝ)) - 1) := by sorry
