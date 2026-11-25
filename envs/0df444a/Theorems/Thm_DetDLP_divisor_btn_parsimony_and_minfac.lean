-- Prove2me | Theorems.Thm_DetDLP_divisor_btn_parsimony_and_minfac
-- name    : DetDLP.divisor_btn_parsimony_and_minfac
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T12:27:06.482943+00:00
-- url     : https://prove2.me/theorems/e031104b-a672-4da4-8fc3-8400623b6390
-- title:
--   Nontrivial Divisor BTN Parsimony and Prefix-Pinned Smallest Prime Factor Extraction
-- statement:
--   Establishes the mathematical core of Proposition 2.6 (deterministic integer factorization):
--
--   For any $N \ge 2$ and $n = \lceil \log_2(N+1)\rceil$: $N < 2^n$; every nontrivial divisor $d \in [2, N)$ uniquely determines $e = N/d \in [2, 2^n)$ with $d e = N$; the nontrivial divisor set is empty iff $N$ is prime; and when $N$ is composite, its minimum nontrivial divisor is `N.minFac`, which is prime and splits `N.primeFactorsList = N.minFac :: (N / N.minFac).primeFactorsList`.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Proof of Proposition 2.6 (pp. 10–11)

import Mathlib
import Definitions.Def_DetDLP_Machine

set_option autoImplicit false

namespace DetDLP

/-- Mathematical core of deterministic integer factorization via divisor-BTN parsimony and
prefix-pinned smallest divisor `N.minFac` (Section 2.3, Proposition 2.6, pp. 10–11):
for every `N ≥ 2` and `n = bitLen (N + 1)`, every nontrivial divisor `d ∈ [2, N)` uniquely
determines `e = N / d < 2^n` with `d * e = N`; the nontrivial divisor set is empty iff `N.Prime`;
and when `N` is composite, its minimum element is `N.minFac`, which is prime and splits
`N.primeFactorsList = N.minFac :: (N / N.minFac).primeFactorsList`. -/
theorem divisor_btn_parsimony_and_minfac :
    ∀ (N : ℕ), 2 ≤ N →
      let n := bitLen (N + 1)
      N < 2 ^ n ∧
      (∀ d e : ℕ,
        (2 ≤ d ∧ d < N ∧ e < 2 ^ n ∧ d * e = N) ↔
        (2 ≤ d ∧ d < N ∧ d ∣ N ∧ e = N / d)) ∧
      ((Finset.Ico 2 N).filter (fun d => d ∣ N) = ∅ ↔ N.Prime) ∧
      (¬ N.Prime →
        N.minFac ∈ (Finset.Ico 2 N).filter (fun d => d ∣ N) ∧
        N.minFac.Prime ∧
        (∀ d ∈ (Finset.Ico 2 N).filter (fun d => d ∣ N), N.minFac ≤ d) ∧
        2 ≤ N / N.minFac ∧ N / N.minFac < N ∧
        N.primeFactorsList = N.minFac :: (N / N.minFac).primeFactorsList) := by sorry

end DetDLP
