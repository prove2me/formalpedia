-- Prove2me | Theorems.Thm_BellmanDP_Allocation_strictly_concave_returns
-- name    : BellmanDP.Allocation.strictly_concave_returns
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T14:13:43.71699+00:00
-- url     : https://prove2.me/theorems/a6080b14-74c7-45aa-a123-59fa16937f9e
-- title:
--   Chapter I, Theorem 5 — strictly concave returns give a strictly concave $f$ and a unique optimal policy
-- statement:
--   Assume the hypotheses of Chapter I, Theorem 1, and in addition that $g$ and $h$ are strictly concave on $[0,\infty)$. Let $f$ be the solution of
--   $$f(x) = \max_{0\le y\le x}\big[g(y)+h(x-y)+f(ay+b(x-y))\big]$$
--   that is continuous at $0$ with $f(0)=0$. Then
--   1. $f$ is strictly concave on $[0,\infty)$;
--   2. the optimal policy is unique: for every $x\ge 0$ there is exactly one $y\in[0,x]$ with $g(y)+h(x-y)+f(ay+b(x-y)) = f(x)$.
--
--   Strict concavity is the setting in which the optimal allocation is a well-defined function $y(x)$, whose structure Theorem 6 of the chapter describes.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter I, Theorem 5, p. 20

import Mathlib
import Definitions.Def_BellmanDP_Allocation_Model

namespace BellmanDP.Allocation

/-- Ch. I, Theorem 5, p. 20. If in addition to the hypotheses of Theorem 1 the functions `g` and
`h` are strictly concave on `x ≥ 0`, then the solution `f` of Theorem 1 is strictly concave on
`x ≥ 0`, and for each `x ≥ 0` the maximizing `y ∈ [0, x]` in (8.1) is unique. -/
theorem strictly_concave_returns (g h : ℝ → ℝ) (a b : ℝ)
    (hyp : AllocationHyp g h a b)
    (hg : StrictConcaveOn ℝ (Set.Ici 0) g) (hh : StrictConcaveOn ℝ (Set.Ici 0) h)
    (f : ℝ → ℝ) (hf : IsAllocationSolution g h a b f)
    (hfc : ContinuousWithinAt f (Set.Ici 0) 0) (hf0 : f 0 = 0) :
    StrictConcaveOn ℝ (Set.Ici 0) f ∧
      ∀ x : ℝ, 0 ≤ x → ∃! y : ℝ, y ∈ Set.Icc 0 x ∧ allocT g h a b f x y = f x := by sorry

end BellmanDP.Allocation
