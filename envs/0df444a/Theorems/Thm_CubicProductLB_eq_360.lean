-- Prove2me | Theorems.Thm_CubicProductLB_eq_360
-- name    : CubicProductLB.eq_360
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:22:49.225131+00:00
-- url     : https://prove2.me/theorems/8e08598b-3ab6-468a-8a36-956c8da7c801
-- title:
--   Eqs. (356)–(360) — reduction to a special length by fixing surplus coordinates to $+1$
-- statement:
--   Let $q > 3$ be the target prime, and for $n \ge 3$ put
--   $$N := 3 \cdot 2^{\lfloor \log_2 \lfloor n/3 \rfloor \rfloor}.$$
--   Then:
--
--   1. $N$ exceeds any fixed threshold for all sufficiently large $n$, and $N \le n < 2N$;
--   2. for $N \le n$ and $x \in X_N$, one has $F_{q,n}(x_1, \dots, x_N, 1, \dots, 1) = F_{q,N}(x_1, \dots, x_N)$;
--   3. for $N \le n$, every cubic representation of $F_{q,n}$ of occurrence cost $C$ yields, by the substitution $x_{N+1} = \cdots = x_n = +1$, a cubic representation of $F_{q,N}$ of occurrence cost $C'$ with $C' \le C$, whose factors are on $X_N$ the restrictions of the original factors.
--
--   This reduces arbitrary lengths to those of the form $3 \cdot 2^d$, and is the reason for the factor two in the exponent.
--
--   **Formalization Note** The floor of the logarithm is `Nat.log 2 (n / 3)`.
--
--   Differences from the source:
--   - generalization: (357) "for all sufficiently large n", and (359), (360) for the N of (356) → (357) for all n ≥ 3, the threshold clause separately, and (359), (360) for every N ≤ n; reason: the inequalities hold from n = 3 on; (359), (360) use only N ≤ n, and every N of (356) qualifies by (357), so the Lean specializes to the page
--   - encoding: ⌊log₂⌊n/3⌋⌋ → Nat.log 2 (n / 3); reason: both are the floor; for n ≥ 3 the argument is positive
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), proof of Theorem 5, Step 5, Eqs. (356)–(360), p.40

import Mathlib
import Definitions.Def_CubicProductLB_signCube
import Definitions.Def_CubicProductLB_signedMod
import Definitions.Def_CubicProductLB_ListedFactor
import Definitions.Def_CubicProductLB_ProductRep
import Definitions.Def_CubicProductLB_CubicRep
import Definitions.Def_CubicProductLB_padOnes

namespace CubicProductLB

/-- Eqs. (356)–(360) (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), proof of Theorem 5, Step 5, Eqs. (356)–(360), p.40). With
`N = 3 · 2^⌊log₂⌊n/3⌋⌋`: `N` tends to infinity with `n`, and `N ≤ n < 2N`. Fixing the surplus coordinates to
`+1` preserves the target, and the restricted factors of a cubic representation of `F_{q,n}` of cost `C`
form a cubic representation of `F_{q,N}` of cost `C' ≤ C`.

**Formalization Note** `⌊log₂⌊n/3⌋⌋` is `Nat.log 2 (n / 3)`, and "sufficiently large" for (357) is `3 ≤ n`
(`Nat.log 2 0 = 0` gives `N = 3 > n` below that). The last clause says that the factors of `r'` are, on
`X_N`, the restrictions of those of `r`, in order. -/
theorem eq_360 (q : ℕ) (hq : q.Prime) (h3 : 3 < q) :
    (∀ N₀ : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, N₀ ≤ 3 * 2 ^ Nat.log 2 (n / 3)) ∧
    (∀ n ≥ 3, 3 * 2 ^ Nat.log 2 (n / 3) ≤ n ∧ n < 2 * (3 * 2 ^ Nat.log 2 (n / 3))) ∧
    (∀ N n : ℕ, N ≤ n → ∀ x ∈ signCube N, signedMod q n (padOnes x) = signedMod q N x) ∧
    (∀ N n : ℕ, N ≤ n → ∀ r : CubicRep q n, ∃ r' : CubicRep q N,
      r'.cost ≤ r.cost ∧
      ∀ x ∈ signCube N,
        (r'.factors.map fun l => ListedFactor.eval l x) =
          r.factors.map fun l => ListedFactor.eval l (padOnes x)) := by sorry

end CubicProductLB
