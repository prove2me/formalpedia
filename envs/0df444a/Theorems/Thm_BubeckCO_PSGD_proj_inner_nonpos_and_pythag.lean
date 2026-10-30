-- Prove2me | Theorems.Thm_BubeckCO_PSGD_proj_inner_nonpos_and_pythag
-- name    : BubeckCO.PSGD.proj_inner_nonpos_and_pythag
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:26:16.077989+00:00
-- url     : https://prove2.me/theorems/48c30da9-da73-404d-a15d-b1f20c97eb65
-- title:
--   Lemma 3.1 — obtuse-angle and Pythagorean inequalities for the projection
-- statement:
--   Let $X \subseteq \mathbb{R}^n$ be compact and convex (the standing assumption of Chapter 3), $\|\cdot\|$ the Euclidean norm and $\Pi_X$ the Euclidean projection onto $X$. For every $x \in X$ and $y \in \mathbb{R}^n$,
--
--   $$
--   (\Pi_X(y) - x)^\top (\Pi_X(y) - y) \le 0
--   \qquad\text{and}\qquad
--   \|\Pi_X(y) - x\|^2 + \|y - \Pi_X(y)\|^2 \le \|y - x\|^2 .
--   $$
--
--   The second inequality says in particular that projecting onto $X$ does not increase the distance to any point of $X$; this is the step of the analysis of projected subgradient descent that controls the projection (3.3).
--
--   **Formalization Note** $\Pi_X(y)$ is encoded as any point $p$ with `IsEuclideanProj X y p`. Both clauses are stated, as a conjunction.
--
--   Differences from the source:
--   - encoding: Π_X(y), the argmin of ‖y − z‖ over z ∈ X → any p with IsEuclideanProj X y p; reason: for non-empty closed convex X (here compact and convex) the argmin exists and is unique, so both describe the same point
-- source:
--   Bubeck, Convex Optimization: Algorithms and Complexity, Found. Trends Mach. Learn. 8(3-4), 2015, p. 263 (PDF p. 36), Lemma 3.1

import Mathlib
import Definitions.Def_BubeckCO_PSGD_IsEuclideanProj

namespace BubeckCO.PSGD

/-- **Lemma 3.1 (projection inequalities).**
Bubeck, Convex Optimization: Algorithms and Complexity, Found. Trends Mach. Learn. 8(3-4), 2015,
p. 263 (PDF p. 36), Lemma 3.1: "Let `x ∈ X` and `y ∈ ℝⁿ`, then
`(Π_X(y) − x)ᵀ(Π_X(y) − y) ≤ 0`, which also implies
`‖Π_X(y) − x‖² + ‖y − Π_X(y)‖² ≤ ‖y − x‖²`."

Under the Chapter 3 standing assumption (`X ⊂ ℝⁿ` compact and convex, p. 262–263), for
`x ∈ X`, `y ∈ ℝⁿ` and `p = Π_X(y)`, both `⟪p − x, p − y⟫ ≤ 0` and
`‖p − x‖² + ‖y − p‖² ≤ ‖y − x‖²` hold.

**Formalization Note.** `ℝⁿ` is `EuclideanSpace ℝ (Fin n)` with the Euclidean norm. `Π_X(y)` is
encoded as any `p` with `IsEuclideanProj X y p`; for non-empty closed convex `X` this `p` exists
and is unique, so it is `Π_X(y)`. Both clauses of the lemma are stated, as a conjunction. -/
theorem proj_inner_nonpos_and_pythag {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hXcompact : IsCompact X) (hXconv : Convex ℝ X)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X) (y p : EuclideanSpace ℝ (Fin n))
    (hp : IsEuclideanProj X y p) :
    inner ℝ (p - x) (p - y) ≤ 0 ∧ ‖p - x‖ ^ 2 + ‖y - p‖ ^ 2 ≤ ‖y - x‖ ^ 2 := by sorry

end BubeckCO.PSGD
