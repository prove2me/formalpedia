-- Prove2me | Theorems.Thm_DiscreteConvex_IntegralConvexity_integral_local_to_global_optimality
-- name    : DiscreteConvex.IntegralConvexity.integral_local_to_global_optimality
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T21:52:04.532802+00:00
-- url     : https://prove2.me/theorems/0e3b6bdb-510b-4db6-9ef7-bf176e05d67b
-- title:
--   Theorem 3.21 -- local optimality characterizes global optimality
-- statement:
--   **Theorem 3.21** (p.94). For an integrally convex function $f : \mathbb Z^n \to \mathbb R \cup \{+\infty\}$ and $x \in \operatorname{dom}_{\mathbb Z} f$,
--
--   $$f(x) \le f(y)\ (\forall y \in \mathbb Z^n) \iff f(x) \le f(x + \chi_Y - \chi_Z)\ (\forall Y, Z \subseteq \{1,\dots,n\}).$$
--
--   Global optimality is equivalent to a finite, uniformly bounded local check: only the (at most) $3^n - 1$ neighbors reachable by adding $+1$ on a subset $Y$ of coordinates and $-1$ on a disjoint subset $Z$ need be checked, however large the effective domain. Restricting the right-hand side to a single fixed $(Y,Z)$, or letting $Y, Z$ range over *all* of $\mathbb Z^n$ rather than just the unit sign pattern, would make the "if" direction trivial or the theorem false; the finite bound $3^n - 1$ over disjoint $Y, Z \subseteq \{1,\dots,n\}$ is the entire content.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.94, Theorem 3.21.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.94, Theorem 3.21

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexity_IntegrallyConvex
import Definitions.Def_DiscreteConvex_IntegralConvexity_DomZ
import Definitions.Def_DiscreteConvex_IntegralConvexity_IndicatorVec

namespace DiscreteConvex.IntegralConvexity

/-- Theorem 3.21 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.94). For an integrally
convex function `f : Zⁿ → R ∪ {+∞}` and `x ∈ dom_Z f`, global optimality of `x` is equivalent
to a finite local check over the (at most) `3ⁿ - 1` neighbors reachable by adding `+1` on a
subset `Y` of coordinates and `-1` on a disjoint subset `Z` of coordinates. -/
theorem integral_local_to_global_optimality {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ)
    (hf : IntegrallyConvex f) (x : Fin n → ℤ) (hx : x ∈ DomZ f) :
    (∀ y : Fin n → ℤ, f x ≤ f y) ↔
      (∀ Y Z : Finset (Fin n),
        f x ≤ f (fun i => x i + IndicatorVec Y i - IndicatorVec Z i)) := by sorry

end DiscreteConvex.IntegralConvexity
