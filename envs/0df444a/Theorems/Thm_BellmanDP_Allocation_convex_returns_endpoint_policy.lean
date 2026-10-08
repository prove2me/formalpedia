-- Prove2me | Theorems.Thm_BellmanDP_Allocation_convex_returns_endpoint_policy
-- name    : BellmanDP.Allocation.convex_returns_endpoint_policy
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T14:13:47.967896+00:00
-- url     : https://prove2.me/theorems/10992eb9-aea5-497a-86b8-6631806a6307
-- title:
--   Chapter I, Theorem 4 — convex returns give a convex $f$ and an all-or-nothing allocation
-- statement:
--   Assume the hypotheses of Chapter I, Theorem 1, and in addition that $g$ and $h$ are convex on $[0,\infty)$. Let $f$ be the solution of
--   $$f(x) = \max_{0\le y\le x}\big[g(y)+h(x-y)+f(ay+b(x-y))\big]$$
--   that is continuous at $0$ with $f(0)=0$. Then
--   1. $f$ is convex on $[0,\infty)$;
--   2. for each $x \ge 0$ the maximum is attained at $y=0$ or at $y=x$; equivalently,
--   $$f(x) = \max\big(g(x) + f(ax),\ h(x) + f(bx)\big).$$
--
--   With convex returns the optimal policy never splits the resource: at every stage everything goes to one of the two activities.
--
--   **Formalization Note** "For each value of $x$, $y$ will equal $0$ or $x$" is stated as: one of the endpoints $y=0$, $y=x$ is a maximizer. It does not claim that every maximizer is an endpoint, which fails e.g. for $g=h=0$.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter I, Theorem 4, p. 19

import Mathlib
import Definitions.Def_BellmanDP_Allocation_Model

namespace BellmanDP.Allocation

/-- Ch. I, Theorem 4, p. 19. If in addition to the hypotheses of Theorem 1 the functions `g` and
`h` are convex on `x ≥ 0`, then the solution `f` of Theorem 1 is convex on `x ≥ 0`, and for each
`x ≥ 0` the maximum in (8.1) is attained at `y = 0` or at `y = x`. -/
theorem convex_returns_endpoint_policy (g h : ℝ → ℝ) (a b : ℝ)
    (hyp : AllocationHyp g h a b)
    (hg : ConvexOn ℝ (Set.Ici 0) g) (hh : ConvexOn ℝ (Set.Ici 0) h)
    (f : ℝ → ℝ) (hf : IsAllocationSolution g h a b f)
    (hfc : ContinuousWithinAt f (Set.Ici 0) 0) (hf0 : f 0 = 0) :
    ConvexOn ℝ (Set.Ici 0) f ∧
      ∀ x : ℝ, 0 ≤ x → (allocT g h a b f x 0 = f x ∨ allocT g h a b f x x = f x) := by sorry

end BellmanDP.Allocation
