-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_main_public_large_small_original_jump_translation_bound
-- name    : AvramDividend.Classical.avram_p3_main_public_large_small_original_jump_translation_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:06:17.357801+00:00
-- url     : https://prove2.me/theorems/d87eca9e-5de4-46f3-9129-b11bc07e2eb0
-- title:
--   Public source-exact finite-grid large/small original negative jump translation bound
-- statement:
--   Public importable replay of the exact already-Proved private P3-D finite-grid original negative jump translation bound. Preserves the nonlinear original source jump, finite large-mark split, and absolute small-mark tail.
-- source:
--   Exact previously accepted private source proof AvramDividend.Classical.avram_p3_d_bvmesh_large_small_jump_translation_bound, UUID 8d317909-b18a-4eac-9a0e-999397dc82ec, submission abf0ca03-766e-4f2e-b095-9215a59d246d, source SHA-256 f5f1398026ad5097530da62cd8de09bbc6a6c8f8960e52f2fc5c4f43d78d18c0; canonical P3 original stopped HJB a19d8b28.

import Mathlib
open scoped BigOperators

theorem AvramDividend.Classical.avram_p3_main_public_large_small_original_jump_translation_bound
    (n : ℕ) (S : Finset ℕ) (f : ℝ → ℝ)
    (r z c j : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hr : ∀ i, i < n → 0 ≤ r i ∧ r i ≤ 1)
    (hlarge : ∀ i, i < n → i ∈ S →
      |f (z i + c i - j i) - f (z i - j i)| ≤ K * |c i| ∧
      |f (z i + c i) - f (z i)| ≤ K * |c i|)
    (hsmall : ∀ i, i < n → i ∉ S →
      |f (z i + c i - j i) - f (z i + c i)| ≤ K * |j i| ∧
      |f (z i - j i) - f (z i)| ≤ K * |j i|) :
    |∑ i ∈ Finset.range n,
      r i * ((f (z i + c i - j i) - f (z i + c i)) -
        (f (z i - j i) - f (z i)))| ≤
      2 * K * (∑ i ∈ Finset.range n,
        if i ∈ S then |c i| else |j i|) := by sorry
