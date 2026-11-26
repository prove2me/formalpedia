-- Prove2me | Theorems.Thm_Erdos287_few_prime_layers_with_few_omissions
-- name    : Erdos287.few_prime_layers_with_few_omissions
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T13:20:01.963816+00:00
-- url     : https://prove2.me/theorems/0cfeea21-b93d-5b4b-9cbb-0b8c4e2c65e8
-- title:
--   Few large-prime layers can have only a small number of omissions
-- statement:
--   Let $D\subseteq[m,M]$ have reciprocal sum one, let $L=\operatorname{lcm}(1,\ldots,B)$, and suppose $BL<Y^{K+1}$. Count the primes $p\ge Y$ with $\lfloor M/p\rfloor\le B$ for which $[m,M]$ contains at least $R$ multiples of $p$ and fewer than $R$ of them are omitted from $D$. There are at most $(B+1)^2K\sum_{j<R}\binom Bj$ such primes.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.few_prime_layers_with_few_omissions (D P : Finset ℕ) (m M B Y K R : ℕ) (hm : 0 < m) (hmM : m ≤ M)
    (hD : D ⊆ Finset.Icc m M) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hY : 2 ≤ Y)
    (hP : ∀ p ∈ P, p.Prime ∧ Y ≤ p ∧ M / p ≤ B ∧
      R ≤ (Finset.Icc ((m - 1) / p + 1) (M / p)).card)
    (hbound : B * ((Finset.Icc 1 B).lcm id) < Y ^ (K + 1)) :
    (P.filter (fun p =>
      ((Finset.Icc ((m - 1) / p + 1) (M / p)).filter (fun c => c * p ∉ D)).card < R)).card
      ≤ ((B + 1) * (B + 1)) * (∑ j ∈ Finset.range R, B.choose j) * K := by sorry
