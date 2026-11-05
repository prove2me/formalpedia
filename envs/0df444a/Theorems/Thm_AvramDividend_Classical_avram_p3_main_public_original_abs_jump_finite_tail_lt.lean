-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_main_public_original_abs_jump_finite_tail_lt
-- name    : AvramDividend.Classical.avram_p3_main_public_original_abs_jump_finite_tail_lt
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:31:48.854106+00:00
-- url     : https://prove2.me/theorems/30e786d4-0325-4b69-a7a1-6037daf69e0d
-- title:
--   Public original BV P3-D finite source negative-jump tail interface
-- statement:
--   Publicly importable source-identical replay of the accepted original bounded-variation negative-jump finite-tail or finite-mark bound; retains exact source jump magnitudes and finite-exclusion accounting without new process assumptions.
-- source:
--   Original accepted private P3-D AvramDividend.Classical.avram_p3_d_bvmesh_original_absolute_jump_finite_exclusion_tail_lt UUID 170607e6-5c51-4953-a431-5a15dc7f2fd2, submission f5667e2d-2016-4bea-9ae4-3285d59730e2, source SHA-256 74f440f29664b0ed46dbcf9eaaaf6a801dbb456ac0cfc8ab3377f5016d3eb19b. Canonical stochastic P3 a19d8b28 requires publicly importable source-tail limits.

import Mathlib
open Filter Set
open scoped BigOperators

theorem AvramDividend.Classical.avram_p3_main_public_original_abs_jump_finite_tail_lt
    {ι : Type*} (j : ι → ℝ)
    (hj : Summable (fun i => |j i|))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset ι, (∑' i : {i : ι // i ∉ S}, |j i.1|) < ε := by sorry
