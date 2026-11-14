-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a202_small_C2_Taylor_remainder_gives_local_Lipschitz
-- name    : AvramDividend.Classical.avram_ga_a202_small_C2_Taylor_remainder_gives_local_Lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:32:06.636491+00:00
-- url     : https://prove2.me/theorems/0fcb5bad-b7d2-4fa9-ab9f-4dd2ecdef68b
-- title:
--   Small classical Gaussian source C2 Taylor remainder and compact jets imply uniform local Lipschitz value increment bound
-- statement:
--   For a real increment r of absolute magnitude at most one, an exact source value difference e, first-derivative coefficient d and Hessian coefficient j uniformly bounded by M, if the second-order Taylor remainder has magnitude at most epsilon times r squared, then the value difference is bounded in absolute value by the uniform local Lipschitz constant three halves M plus epsilon, times the raw increment magnitude. This is the deterministic connection from the original stopped C2 Taylor modulus a190 and compact jet estimate a165 to the small-step Lipschitz hypothesis of the safe discount correction a199, bypassing the overly general original a151.
-- source:
--   Absolute triangle inequality, classical Taylor remainder estimate and compact C2 derivative bounds.

import Mathlib
open Real
noncomputable section

theorem AvramDividend.Classical.avram_ga_a202_small_C2_Taylor_remainder_gives_local_Lipschitz
    (e d j r ε M : ℝ)
    (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hd : |d| ≤ M) (hj : |j| ≤ M)
    (hr : |r| ≤ 1)
    (hTaylor : |e - d * r - j * r^2 / 2| ≤ ε * r^2) :
    |e| ≤ (3 * M / 2 + ε) * |r| := by sorry
