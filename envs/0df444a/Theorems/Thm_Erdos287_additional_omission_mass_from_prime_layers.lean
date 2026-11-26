-- Prove2me | Theorems.Thm_Erdos287_additional_omission_mass_from_prime_layers
-- name    : Erdos287.additional_omission_mass_from_prime_layers
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T13:21:42.035604+00:00
-- url     : https://prove2.me/theorems/bd5a55b6-ae25-5b92-8c6d-ec7bab461043
-- title:
--   Additional reciprocal mass forced by disjoint prime layers
-- statement:
--   Let $D\subseteq[m,M]$ have reciprocal sum one, and let $H$ be a set of already established omissions within $[m,M]$. Let $P$ be a finite set of primes at least $Y$ with $M<Y^2$. Suppose that no member of $H$ is divisible by a member of $P$ and that the interval omits at least $R$ multiples of each prime in $P$. Then the full interval has reciprocal mass at least $1+\sum_{n\in H}1/n+R|P|/M$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.additional_omission_mass_from_prime_layers (D H P : Finset ℕ) (m M Y R : ℕ) (hm : 0 < m) (hmM : m ≤ M)
    (hD : D ⊆ Finset.Icc m M) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hH : H ⊆ Finset.Icc m M) (hHD : Disjoint H D)
    (hYM : M < Y ^ 2) (hP : ∀ p ∈ P, p.Prime ∧ Y ≤ p)
    (hsep : ∀ p ∈ P, ∀ n ∈ H, ¬ p ∣ n)
    (hR : ∀ p ∈ P, R ≤
      ((Finset.Icc ((m - 1) / p + 1) (M / p)).filter (fun c => c * p ∉ D)).card) :
    1 + (∑ n ∈ H, (1 : ℚ) / n) + ((R * P.card : ℕ) : ℚ) / M
      ≤ ∑ n ∈ Finset.Icc m M, (1 : ℚ) / n := by sorry
