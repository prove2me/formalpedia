-- Prove2me | Theorems.Thm_Dubner_grimmelt_teravainen_theorem_1_1
-- name    : Dubner.grimmelt_teravainen_theorem_1_1
-- status  : Open
-- author  : @Idealson
-- created : 2026-11-24T12:00:48.103248+00:00
-- url     : https://prove2.me/theorems/5e3468c6-1202-4d12-9ab0-09790831362a
-- title:
--   Grimmelt–Teräväinen: almost all $m\equiv4\pmod 6$ are sums of two Chen primes
-- statement:
--   There is a constant $\delta>0$ such that all but $O(N^{1-\delta})$ natural numbers $m\le N$ with $m\equiv4\pmod 6$ are the sum of two Chen primes, where a Chen prime is a prime $p$ such that $p+2$ is a product of at most two primes. Explicitly, there are $\delta>0$ and $C$ with
--
--   $$\#\{m\le N:\ m\equiv4\ (\mathrm{mod}\ 6),\ m\ne p+q \text{ for all Chen primes } p,q\}\le C\,N^{1-\delta}\quad(N\ge1).$$
--
--   This is the binary, almost-all, almost-twin analogue of Dubner's conjecture; the authors note it is optimal barring substantial progress on the twin prime or binary Goldbach conjectures.
-- source:
--   M. Grimmelt, J. Teräväinen, The Exceptional Set in Goldbach's Problem with two Chen Primes, arXiv:2508.16400 (2025), Theorem 1.1

import Mathlib
import Definitions.Def_Dubner_TwinPrimes

namespace Dubner
theorem grimmelt_teravainen_theorem_1_1 :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      ({m : ℕ | m ≤ N ∧ m % 6 = 4 ∧
          ¬ ∃ p q : ℕ, IsChenPrime p ∧ IsChenPrime q ∧ m = p + q}.ncard : ℝ) ≤
        C * (N : ℝ) ^ (1 - δ) := by
  sorry
end Dubner
