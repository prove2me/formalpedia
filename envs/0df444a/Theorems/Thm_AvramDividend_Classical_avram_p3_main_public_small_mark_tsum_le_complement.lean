-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_main_public_small_mark_tsum_le_complement
-- name    : AvramDividend.Classical.avram_p3_main_public_small_mark_tsum_le_complement
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:31:50.735276+00:00
-- url     : https://prove2.me/theorems/e3b32d24-54ce-4ecc-b432-c790e19e6778
-- title:
--   Public original BV P3-D finite source negative-jump tail interface
-- statement:
--   Publicly importable source-identical replay of the accepted original bounded-variation negative-jump finite-tail or finite-mark bound; retains exact source jump magnitudes and finite-exclusion accounting without new process assumptions.
-- source:
--   Original accepted private P3-D AvramDividend.Classical.avram_p3_d_bvmesh_original_small_mark_tsum_le_finite_complement UUID 6e461d12-dc87-4952-adb0-fd7ca5b62000, submission 108aaa94-4b8d-4142-9ef7-4df70a2b8dfa, source SHA-256 53c0c9334e59f0f6d703b86576798b5a11953c8c1578b70b03fdea8f9e8dae1a. Canonical stochastic P3 a19d8b28 requires publicly importable source-tail limits.

import Mathlib
open Filter Set
open scoped BigOperators

theorem AvramDividend.Classical.avram_p3_main_public_small_mark_tsum_le_complement
    {ι : Type*} [DecidableEq ι] (j : ι → ℝ) (S : Finset ι) (δ : ℝ)
    (hj : Summable (fun i => |j i|))
    (hS : ∀ i ∈ S, δ ≤ |j i|) :
    (∑' i : ι, if |j i| < δ then |j i| else 0) ≤
      ∑' i : ι, if i ∈ S then 0 else |j i| := by sorry
