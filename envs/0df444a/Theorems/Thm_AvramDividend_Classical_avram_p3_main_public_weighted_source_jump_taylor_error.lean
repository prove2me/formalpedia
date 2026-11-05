-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_main_public_weighted_source_jump_taylor_error
-- name    : AvramDividend.Classical.avram_p3_main_public_weighted_source_jump_taylor_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:56:52.69265+00:00
-- url     : https://prove2.me/theorems/aab7abee-5bd9-43cb-b2c6-fbd620fb1ed4
-- title:
--   Public original BV weighted source-jump Taylor remainder bound for P3 C1 mesh
-- statement:
--   Re-publish the mathematically identical, independently source-proved exact finite-grid weighted Taylor error, keeping nonlinear original negative-jump increments unlinearised as a public importable interface. The exact original theorem is private on Prove2Me and cannot be imported by the public original BV HJB core; the complete accepted proof is replayed.
-- source:
--   Accepted private P3-D theorem AvramDividend.Classical.avram_p3_d_bvmesh_weighted_source_jump_taylor_error, UUID 67a48979-c386-4419-8fbf-252f0855228c, submission 81f2981a-1610-49ea-92d4-24cebb833172, exact source SHA-256 0af3970e7cd36c9e8b0ccf425f91ea0a77f20e26241f3cb5143bd95b4bf42588; project original BV P3 target a19d8b28.

import Mathlib
open scoped BigOperators

theorem AvramDividend.Classical.avram_p3_main_public_weighted_source_jump_taylor_error
    (f : ℝ → ℝ) (n : ℕ)
    (r z cont jump delta : ℕ → ℝ)
    (ε B : ℝ) (hε : 0 ≤ ε)
    (hstep : ∀ i, i < n → delta i = cont i - jump i)
    (hr : ∀ i, i < n → 0 ≤ r i ∧ r i ≤ 1)
    (htaylor : ∀ i, i < n →
      |f (z i + cont i) - f (z i) - deriv f (z i) * cont i| ≤
        ε * |cont i|)
    (hvar : (∑ i ∈ Finset.range n, |cont i|) ≤ B) :
    |∑ i ∈ Finset.range n,
      r i * ((f (z i + delta i) - f (z i)) -
        (f (z i + cont i - jump i) - f (z i + cont i)) -
        deriv f (z i) * cont i)| ≤ ε * B := by sorry
