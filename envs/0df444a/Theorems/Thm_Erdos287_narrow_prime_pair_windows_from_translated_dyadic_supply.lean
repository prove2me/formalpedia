-- Prove2me | Theorems.Thm_Erdos287_narrow_prime_pair_windows_from_translated_dyadic_supply
-- name    : Erdos287.narrow_prime_pair_windows_from_translated_dyadic_supply
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T08:06:46.698553+00:00
-- url     : https://prove2.me/theorems/c5229566-ca9a-4d9d-bccb-0cefa136a838
-- title:
--   Uniform translated dyadic prime supply implies arbitrarily narrow fixed relative windows
-- statement:
--   Suppose for each fixed $C$ and all sufficiently large $H$, every translate $0\le z\le CH$ of a given affine family has two prime values at some parameter $H<n\le2H$. Then for each positive integer $q$, the original family has two prime values at some $T<t\le T+\lfloor T/q\rfloor$ for every sufficiently large $T$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. External affine sieve input: https://ford126.web.illinois.edu/sieve2023.pdf.

import Mathlib

theorem Erdos287.narrow_prime_pair_windows_from_translated_dyadic_supply (a : ℕ → ℕ) (N q : ℕ) (hq : 1 ≤ q)
    (hdyadic : ∀ C : ℕ, ∃ H₀ : ℕ, ∀ H : ℕ, H₀ ≤ H → ∀ z : ℕ, z ≤ C * H →
      ∃ n : ℕ, H < n ∧ n ≤ 2 * H ∧ ∃ i j : ℕ, i < j ∧ j < N ∧
        Nat.Prime (a i * (n + z) + 1) ∧ Nat.Prime (a j * (n + z) + 1)) :
    ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T →
      ∃ t : ℕ, T < t ∧ t ≤ T + T / q ∧ ∃ i j : ℕ, i < j ∧ j < N ∧
        Nat.Prime (a i * t + 1) ∧ Nat.Prime (a j * t + 1) := by sorry
