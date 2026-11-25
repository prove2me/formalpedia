-- Prove2me | Theorems.Thm_DetDLP_splitting_tree_size_and_prime_power_from_factors
-- name    : DetDLP.splitting_tree_size_and_prime_power_from_factors
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T14:02:51.560486+00:00
-- url     : https://prove2.me/theorems/3ab8983e-5875-44af-b22a-3ae923d65267
-- title:
--   Polynomial Splitting-Tree Leaf Count Bound and Prime-Factor Set Recovery from Factorization Lists
-- statement:
--   Proves two key structural properties for the Proposition 2.6 factor-splitting driver and the Proposition 3.3 prime-power component scan:
--
--   1. **Linear leaf count of the depth-$n$ divisor-splitting tree:** for any proper-divisor function $f : \mathbb{N} \to \mathbb{N}$ and depth-$k$ recursive splitting tree $\mathrm{split}(k, x)$, every $x \ge 2$ satisfies $1 \le |\mathrm{split}(k, x)|$ and $2^{|\mathrm{split}(k, x)|} \le x$; consequently, for $n = \lceil \log_2(N+1)\rceil$, $|\mathrm{split}(n, N)| \le n$ (at most $n$ leaves and $2n-1$ recursive nodes);
--   2. **Prime-factor recovery from `primeFactorsList`:** for every integer $n \ge 1$, the set of distinct prime factors $\mathrm{primeFactors}(n)$ coincides with the support of $\mathrm{primeFactorsList}(n)$, $\prod \mathrm{primeFactorsList}(n) = n$, and $|\mathrm{primeFactors}(n)| \le |\mathrm{primeFactorsList}(n)|$.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3 Proposition 2.6 & Section 3.3 Proposition 3.3 (pp. 10–11, 14)

import Mathlib
import Definitions.Def_DetDLP_Machine

set_option autoImplicit false

namespace DetDLP

/-- Polynomial recursion-tree size bound for Proposition 2.6 and prime-factor list recovery for
Proposition 3.3 (Sections 2.3 & 3.3, pp. 10–11, 14):
1. For any proper-divisor function `f : ℕ → ℕ`, the recursive divisor-splitting tree `split k x`
   satisfies `1 ≤ (split k x).length` and `2 ^ (split k x).length ≤ x` for every `x ≥ 2`; in
   particular, for `n = bitLen (N + 1)`, `(split n N).length ≤ n` (at most `n` leaves).
2. For every `n ≥ 1`, the prime factor set `n.primeFactors` and product `n` are directly
   recovered from `n.primeFactorsList`, with `n.primeFactors.card ≤ n.primeFactorsList.length`. -/
theorem splitting_tree_size_and_prime_power_from_factors :
    (∀ (f : ℕ → ℕ),
      let split : ℕ → ℕ → List ℕ :=
        Nat.rec (motive := fun _ => ℕ → List ℕ) (fun x => [x]) (fun _ prev x =>
          let d := f x
          if 2 ≤ d ∧ d < x ∧ d ∣ x then prev d ++ prev (x / d) else [x])
      (∀ (k x : ℕ), 2 ≤ x → 1 ≤ (split k x).length ∧ 2 ^ (split k x).length ≤ x) ∧
      (∀ (N : ℕ), 2 ≤ N →
        let n := bitLen (N + 1)
        (split n N).length ≤ n)) ∧
    (∀ (n : ℕ), 1 ≤ n →
      (∀ r : ℕ, r ∈ n.primeFactors ↔ r ∈ n.primeFactorsList) ∧
      n.primeFactorsList.prod = n ∧
      n.primeFactors.card ≤ n.primeFactorsList.length) := by
  sorry

end DetDLP
