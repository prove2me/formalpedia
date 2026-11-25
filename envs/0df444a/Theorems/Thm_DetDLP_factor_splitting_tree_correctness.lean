-- Prove2me | Theorems.Thm_DetDLP_factor_splitting_tree_correctness
-- name    : DetDLP.factor_splitting_tree_correctness
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T13:33:16.193793+00:00
-- url     : https://prove2.me/theorems/c7e75338-53ec-4453-85e8-58059d756985
-- title:
--   Soundness of the Depth-n Recursive Divisor-Splitting Tree and Sorted Prime Factorization
-- statement:
--   Let $f : \mathbb{N} \to \mathbb{N}$ be any proper-divisor oracle satisfying $2 \le f(x) < x$ and $f(x) \mid x$ for every composite integer $x \ge 2$, and define the depth-$k$ recursive splitting tree $$\mathrm{split}(0, x) = [x], \qquad \mathrm{split}(k+1, x) = \begin{cases} \mathrm{split}(k, f(x)) \mathbin{++} \mathrm{split}(k, x/f(x)) & \text{if } 2 \le f(x) < x \text{ and } f(x) \mid x, \\ [x] & \text{otherwise.} \end{cases}$$ Because every nontrivial divisor split satisfies $f(x) \le x/2$ and $x/f(x) \le x/2$, for every integer $N \ge 2$ and binary length $n = \lceil \log_2(N+1) \rceil$, the leaves of $\mathrm{split}(n, N)$ are all prime, their product equals $N$, and sorting $\mathrm{split}(n, N)$ in nondecreasing order yields the canonical prime factorization list of $N$.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3 Proposition 2.6 (pp. 10–11)

import Mathlib
import Definitions.Def_DetDLP_Machine

set_option autoImplicit false

namespace DetDLP

/-- Soundness of the depth-`n` recursive divisor-splitting tree (`n = bitLen (N + 1)`):
for any proper-divisor oracle `f : ℕ → ℕ` satisfying
`∀ N ≥ 2, ¬ N.Prime → 2 ≤ f N ∧ f N < N ∧ f N ∣ N`, every proper split halves both factors
(`d ≤ x / 2` and `x / d ≤ x / 2`), so within depth `n = ⌈log₂(N + 1)⌉` the recursion reaches
prime leaves whose product is `N`, and sorting the leaves produces `N.primeFactorsList`. -/
theorem factor_splitting_tree_correctness :
    ∀ (f : ℕ → ℕ),
      (∀ N : ℕ, 2 ≤ N → ¬ N.Prime → 2 ≤ f N ∧ f N < N ∧ f N ∣ N) →
      let split : ℕ → ℕ → List ℕ :=
        Nat.rec (motive := fun _ => ℕ → List ℕ) (fun x => [x]) (fun _ prev x =>
          let d := f x
          if 2 ≤ d ∧ d < x ∧ d ∣ x then prev d ++ prev (x / d) else [x])
      ∀ N : ℕ, 2 ≤ N →
        let n := bitLen (N + 1)
        (split n N).prod = N ∧
        (∀ p ∈ split n N, p.Prime) ∧
        ((split n N).mergeSort) = N.primeFactorsList := by
  sorry

end DetDLP
