-- Prove2me | Theorems.Thm_BregmanDistance_nonneg
-- name    : BregmanDistance.nonneg
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-26T14:35:43.9087+00:00
-- url     : https://prove2.me/theorems/f5bbc851-6018-4fb5-9508-9cff43222893
-- title:
--   The $D$-function of a Bregman function is nonnegative: $D(x,y)\ge 0$
-- statement:
--   Let $h$ be a Bregman function with open zone $S$ (Eckstein, Definition 1). Then for every $x \in \operatorname{cl} S$ and every $y \in S$,
--
--   $$
--   D(x,y) \;=\; h(x) - h(y) - \langle \nabla h(y),\, x-y \rangle \;\ge\; 0 .
--   $$
--
--   Nonnegativity is what lets $D$ be read as a distance-like quantity even though it is neither symmetric nor subject to a triangle inequality, and it is the base case of every Fej\'er-monotonicity argument: once a sequence satisfies $D(z, p^{k+1}) \le D(z, p^k)$ for a reference point $z$, nonnegativity turns the monotone sequence $k \mapsto D(z, p^k)$ into a convergent one and makes the increments summable.
--
--   It is exactly the support inequality of the previous result rearranged, so it holds on the same asymmetric domain: the first argument may sit on the boundary of the zone, the second must lie in its interior, where $\nabla h$ is defined.
--
--   **Formalization Note** A one-line consequence of `BregmanDistance.gradient_support` after unfolding `bregmanD`.
-- source:
--   The basic nonnegativity of the $D$-function in Eckstein, Nonlinear Proximal Point Algorithms Using Bregman Functions, with Applications to Convex Programming, Math. Oper. Res. 18(1) (1993) 202-226, DOI 10.1287/moor.18.1.202, Section 2, pp. 204-205 (immediate from Definition 1).

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model

open BregmanPPA.Convergence ThreeOpSplitting.Convergence Filter Topology

namespace BregmanDistance

/-- The D-function of a Bregman function is nonnegative. -/
theorem nonneg {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (S : Set H) (h : H → ℝ)
    (hh : IsBregmanFunction S h) {x y : H} (hx : x ∈ closure S) (hy : y ∈ S) :
    0 ≤ bregmanD h x y := by sorry

end BregmanDistance
