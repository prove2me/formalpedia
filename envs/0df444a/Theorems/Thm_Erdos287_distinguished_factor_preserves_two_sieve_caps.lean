-- Prove2me | Theorems.Thm_Erdos287_distinguished_factor_preserves_two_sieve_caps
-- name    : Erdos287.distinguished_factor_preserves_two_sieve_caps
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T19:02:49.558751+00:00
-- url     : https://prove2.me/theorems/057f3803-16cb-5a58-86e7-ea43f38891a9
-- title:
--   A distinguished sieve factor preserves the two factor caps
-- statement:
--   Suppose $P\geq1$, $D\geq P^2$, and $p$ is an arithmetic weight supported on integers at most $P$ whose prime factors are all at least $Z$. If $w$ admits Dirichlet-convolution factorizations for every pair of caps with product $D/P$, with the same restriction on prime factors in its second factor, then $p*w$ admits such a factorization for every pair of caps with product $D$.
-- source:
--   Erdős #287, insertion of the distinguished prime in the lower Chen sieve.

import Mathlib

theorem Erdos287.distinguished_factor_preserves_two_sieve_caps (D P A B : ℝ) (Z : ℕ) (hP : 1 ≤ P) (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hAB : A * B = D) (hPD : P ^ 2 ≤ D) (p w : ArithmeticFunction ℝ)
    (hp : ∀ n : ℕ, p n ≠ 0 → (n : ℝ) ≤ P)
    (hpZ : ∀ n : ℕ, p n ≠ 0 → ∀ q : ℕ, q.Prime → q ∣ n → Z ≤ q)
    (hw : ∀ U V : ℝ, 1 ≤ U → 1 ≤ V → U * V = D / P →
      ∃ f g : ArithmeticFunction ℝ, w = f * g ∧
        (∀ n : ℕ, f n ≠ 0 → (n : ℝ) ≤ U) ∧ (∀ n : ℕ, g n ≠ 0 → (n : ℝ) ≤ V) ∧
        (∀ n : ℕ, g n ≠ 0 → ∀ q : ℕ, q.Prime → q ∣ n → Z ≤ q)) :
    ∃ f g : ArithmeticFunction ℝ, p * w = f * g ∧
      (∀ n : ℕ, f n ≠ 0 → (n : ℝ) ≤ A) ∧ (∀ n : ℕ, g n ≠ 0 → (n : ℝ) ≤ B) ∧
      (∀ n : ℕ, g n ≠ 0 → ∀ q : ℕ, q.Prime → q ∣ n → Z ≤ q) := by sorry
