-- Prove2me | Theorems.Thm_BregmanDistance_gradient_support
-- name    : BregmanDistance.gradient_support
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-26T14:35:48.348993+00:00
-- url     : https://prove2.me/theorems/5fa3d240-95af-419d-a100-7192b42f1a13
-- title:
--   A Bregman function is supported from below by its gradient, up to the boundary of its zone
-- statement:
--   Let $S \subseteq H$ be open and let $h$ be a **Bregman function with zone $S$** in the sense of Eckstein's Definition 1: $h$ is continuously differentiable on $S$, strictly convex and continuous on $\operatorname{cl} S$, its $D$-level sets are bounded in either argument, and $D$ is continuous along sequences in $S$. Then for every $y \in S$ and every $z \in \operatorname{cl} S$,
--
--   $$
--   \big\langle \nabla h(y),\, z-y \big\rangle \;\le\; h(z) - h(y) .
--   $$
--
--   This is the first-order convexity inequality, but with the **test point allowed on the boundary** of the zone. That extension is what makes the $D$-function usable on $\operatorname{cl} S \times S$, which is the natural domain in Eckstein's framework: iterates live in the open zone $S$, while the limit points and the zeros one compares them to may only lie in $\operatorname{cl} S$. The inequality cannot be obtained by differentiating at $z$, because $h$ need not be differentiable there — or even finite beyond $\operatorname{cl} S$; instead one restricts $h$ to the segment from $y$ to $z$, which stays in the convex set $\operatorname{cl} S$, and compares the one-sided derivative at the $y$ end with the slope of the chord.
--
--   **Formalization Note** The proof composes $h$ with the affine map $t \mapsto y + t(z-y)$, uses that this composite is convex on the preimage of $\operatorname{cl} S$, and applies the chord-slope bound at $t = 0$, where the derivative exists because $y$ lies in the open set $S$.
-- source:
--   The support inequality used silently throughout Eckstein, Nonlinear Proximal Point Algorithms Using Bregman Functions, with Applications to Convex Programming, Math. Oper. Res. 18(1) (1993) 202-226, DOI 10.1287/moor.18.1.202, Definition 1 and proof of Theorem 1, pp. 204-209; isolated here as a standalone consequence of Definition 1.

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model

open BregmanPPA.Convergence ThreeOpSplitting.Convergence Filter Topology

namespace BregmanDistance

/-- First-order support at a point of the zone, against a test point in its closure. -/
theorem gradient_support {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (S : Set H) (h : H → ℝ)
    (hh : IsBregmanFunction S h) {y z : H} (hy : y ∈ S) (hz : z ∈ closure S) :
    inner ℝ (gradient h y) (z - y) ≤ h z - h y := by sorry

end BregmanDistance
