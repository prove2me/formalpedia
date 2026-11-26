-- Prove2me | Theorems.Thm_Erdos287_two_nested_divisor_restrictions_bound
-- name    : Erdos287.two_nested_divisor_restrictions_bound
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T15:15:40.384891+00:00
-- url     : https://prove2.me/theorems/94ce4867-a38e-47a7-8e2d-0843b2c95971
-- title:
--   Two nested divisor restrictions for nonnegative weights
-- statement:
--   Let $S,K,F$ be finite subsets of $[1,N]$. If $w$ is nonnegative and submultiplicative, and $z$ is nonnegative, then $\sum_{s\in S}w(s)\sum_{k\in K,\ k\mid s}\sum_{f\in F,\ f\mid k}z(f)\le (\sum_{n=1}^N w(n))^2 \sum_{f\in F}w(f)z(f)$.
-- source:
--   Conductor reduction for the Erdős 287 grouped sieve.

import Mathlib

theorem Erdos287.two_nested_divisor_restrictions_bound (N : ℕ) (S K F : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 N) (hK : K ⊆ Finset.Icc 1 N) (hF : F ⊆ Finset.Icc 1 N)
    (w z : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (hz : ∀ n, 0 ≤ z n)
    (hmul : ∀ a b, w (a * b) ≤ w a * w b) :
    (∑ s ∈ S, w s * ∑ k ∈ K.filter (· ∣ s), ∑ f ∈ F.filter (· ∣ k), z f) ≤
    (∑ n ∈ Finset.Icc 1 N, w n) ^ 2 * ∑ f ∈ F, w f * z f := by sorry
