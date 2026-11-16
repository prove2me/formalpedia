-- Prove2me | Theorems.Thm_FasterPrimeEnum_Supplement_theorem_8_7
-- name    : FasterPrimeEnum.Supplement.theorem_8_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:54:30.531746+00:00
-- url     : https://prove2.me/theorems/4ed420b7-9a1b-4016-83dd-0767102ff9ef
-- title:
--   Theorem 8.7 — Selberg-sieve bound for $k<X$ with $Uk+u_1,\dots,Uk+u_g$ all square-$z$-rough
-- statement:
--   There is an absolute constant $C_1>1$ with the following property. Let $g,U$ be positive integers and $u=(u_1,\dots,u_g)$ pairwise distinct integers with $0\le u_i<U$; let $Q=Q(u)$ be the product of the bad primes and $\Delta=\Delta(u)$ the product (8.4), and put $\theta=\theta(g,Q)=g^2\log5Q\log\log5Q$. Then for every integer $X\ge1$ and every real $z>e^{C_1\theta}$, the number of integers $k\in[0,X)$ such that $Uk+u_1,\dots,Uk+u_g$ are all square-$z$-rough is at most
--
--   $$
--   \frac{g!\,\Delta X}{(\log z)^g}\Big(1+O\Big(\frac{\theta}{\log z}\Big)\Big)+O\Big(\frac{z^2(\log z)^{4g}}{((2g)!)^2}\Big),
--   $$
--
--   where the implied constants are absolute (independent of $g$, $U$, $u$, $X$, $z$).
--
--   Summed over all tuples $u$, this gives Theorem 8.2: intervals holding many square-rough integers are rare, which bounds the cost of the repair steps of the rigorous algorithms.
--
--   **Formalization Note** $C_1$ and one constant $K$ for both $O$-terms are fixed before all other quantities; the first $O$ is read as the upper bound $1+K\theta/\log z$.
--
--   Differences from the source:
--   - encoding: the g-tuple u = (u₁, …, u_g) of pairwise distinct integers → an injective u : Fin g → ℕ (0-based index); reason: the same tuples; 0 ≤ u_i is automatic in ℕ
--   - reading: (1 + O(θ/log z)) + O(z²(log z)^{4g}/(2g)!²) with absolute implied constants → (1 + K θ/log z) + K z²(log z)^{4g}/((2g)!)², one K > 0 chosen with C₁ before g, U, u, X, z; reason: the statement is an upper bound; one constant for two O-terms is equivalent (take the larger); (2g)!² is the square of the factorial, as the rendered page and the proof show
--   - encoding: Δ(u) = ∏_p (1 − |B_p|/p²)(1 − 1/p)^{−g} over all primes; Q(u) = ∏_{p bad} p → Delta: Mathlib's unconditional product ∏' over Nat.Primes; Qbad: the product of the bad primes p ≤ max(U, 4g²); reason: the product is 0 when a factor vanishes and absolutely convergent otherwise (p.69, Corollary 8.25), so ∏' is its value; under the hypotheses every bad prime is at most max(U, 4g²)
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), Theorem 8.7, p.69; §8.1, eqs. (8.3)–(8.5), pp.68–69

import Mathlib
import Definitions.Def_FasterPrimeEnum_IsRough
import Definitions.Def_FasterPrimeEnum_Supplement_Delta

set_option autoImplicit false

namespace FasterPrimeEnum

namespace Supplement

open Classical in
/-- **Theorem 8.7** — D. Harvey, *Faster enumeration of primes*, arXiv:2606.22851 (held version,
sha256 7fc13f17…), p.69.

"There exists an absolute constant C₁ > 1 with the following property. Let g, U,
u = (u₁, …, u_g), Q = Q(u) and Δ = Δ(u) be as above. Let (8.5) θ = θ(g, Q) := g² log 5Q log log 5Q.
Then for any integer X ⩾ 1 and any real number z > e^{C₁θ}, the number of integers k ∈ [0, X) such
that Uk + u₁, …, Uk + u_g are all square-z-rough is at most
(g!ΔX / (log z)^g)(1 + O(θ / log z)) + O(z²(log z)^{4g} / (2g)!²)."

"As above" (§8.1, p.68): "Let g and U be positive integers, and fix a g-tuple of pairwise distinct
integers u = (u₁, …, u_g) such that 0 ⩽ u_i < U for all i." `Q(u)` is the product of the bad primes
and `Δ(u)` the product (8.4) (p.69). p.69: "the implied big-O constants in the following result are
absolute, and do not depend on g, U, or u."

**Formalization Note.** `C₁` and one constant `K` for both `O`-terms are chosen before
`g, U, u, X, z`. The bound is an upper bound, so `1 + O(θ/log z)` is `1 + Kθ/log z`. `(2g)!²` is
`((2g)!)²`. The tuple `u` is indexed by `Fin g` (0-based) and injective; square-`z`-rough is the
published `IsSquareRough` (zero is not square-rough, Remark 8.5). Logarithms are natural. -/
theorem theorem_8_7 :
    ∃ C₁ : ℝ, 1 < C₁ ∧ ∃ K : ℝ, 0 < K ∧
      ∀ g U : ℕ, 0 < g → 0 < U → ∀ u : Fin g → ℕ, Function.Injective u → (∀ i, u i < U) →
        ∀ X : ℕ, 1 ≤ X → ∀ z : ℝ, Real.exp (C₁ * theta g (Qbad U u)) < z →
          ((((Finset.range X).filter fun k => ∀ i : Fin g, IsSquareRough z (U * k + u i)).card
              : ℕ) : ℝ) ≤
            ((g.factorial : ℝ) * Delta U u * X / Real.log z ^ g) *
                (1 + K * theta g (Qbad U u) / Real.log z) +
              K * (z ^ 2 * Real.log z ^ (4 * g) / ((Nat.factorial (2 * g) : ℝ) ^ 2)) := by sorry

end Supplement

end FasterPrimeEnum
