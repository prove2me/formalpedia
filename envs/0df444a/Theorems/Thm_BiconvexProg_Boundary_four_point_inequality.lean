-- Prove2me | Theorems.Thm_BiconvexProg_Boundary_four_point_inequality
-- name    : BiconvexProg.Boundary.four_point_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T17:49:28.500975+00:00
-- url     : https://prove2.me/theorems/2e20b59c-eb37-4c59-909e-772fe303d43a
-- title:
--   Proof of Theorem 1: the biconcave four-point inequality at the midpoint
-- statement:
--   Let $S \subseteq \mathbb{R}^p \times \mathbb{R}^q$ and let $\varphi$ be biconcave over $S$ (concave in $x$ and in $y$ separately on every segment of $S$ parallel to a block). Let $x^*, s \in \mathbb{R}^p$ and $y^*, t \in \mathbb{R}^q$, and assume the three segments
--
--   $$[x^*, s] \times \{\tfrac12 y^* + \tfrac12 t\}, \qquad \{x^*\} \times [y^*, t], \qquad \{s\} \times [y^*, t]$$
--
--   lie in $S$. Then
--
--   $$\varphi\big(\tfrac12(x^*, y^*) + \tfrac12(s, t)\big) \ge \tfrac12\varphi(x^*, \tfrac12 y^* + \tfrac12 t) + \tfrac12\varphi(s, \tfrac12 y^* + \tfrac12 t) \ge \tfrac14\big[\varphi(x^*, y^*) + \varphi(x^*, t) + \varphi(s, y^*) + \varphi(s, t)\big].$$
--
--   This is the first display of the proof of Theorem 1: the value of a biconcave function at the centre of a "rectangle" is at least the average of its values at the four corners.
--
--   **Formalization Note** The paper applies the inequality to the points of the previous step, where the segments lie in $S$ because they lie in a Euclidean ball contained in $S$; here the three segment conditions are hypotheses, which is exactly what the two concavity steps use.
-- source:
--   Al-Khayyal, Falk, Jointly Constrained Biconvex Programming, Math. Oper. Res. 8(2), 1983, p. 275, Proof of Theorem 1, first display

import Mathlib
import Definitions.Def_BiconvexProg_Boundary_BiconcaveOn

namespace BiconvexProg.Boundary

/-- First display of the proof of Theorem 1 (Al-Khayyal–Falk 1983, p. 275): for `φ` biconcave
over `S`, and points `(x*, y*)`, `(s, t)` such that the segments `[x*, s] × {½y* + ½t}`,
`{x*} × [y*, t]` and `{s} × [y*, t]` lie in `S`,
`φ(½(x*, y*) + ½(s, t)) ≥ ½φ(x*, ½y* + ½t) + ½φ(s, ½y* + ½t)
  ≥ ¼[φ(x*, y*) + φ(x*, t) + φ(s, y*) + φ(s, t)]`. -/
theorem four_point_inequality {p q : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)))
    (φ : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q) → ℝ) (hφ : BiconcaveOn S φ)
    (xstar s : EuclideanSpace ℝ (Fin p)) (ystar t : EuclideanSpace ℝ (Fin q))
    (h₁ : ∀ x ∈ segment ℝ xstar s, (x, (1 / 2 : ℝ) • ystar + (1 / 2 : ℝ) • t) ∈ S)
    (h₂ : ∀ y ∈ segment ℝ ystar t, (xstar, y) ∈ S)
    (h₃ : ∀ y ∈ segment ℝ ystar t, (s, y) ∈ S) :
    (1 / 2 : ℝ) * φ (xstar, (1 / 2 : ℝ) • ystar + (1 / 2 : ℝ) • t) +
        (1 / 2 : ℝ) * φ (s, (1 / 2 : ℝ) • ystar + (1 / 2 : ℝ) • t) ≤
      φ ((1 / 2 : ℝ) • (xstar, ystar) + (1 / 2 : ℝ) • (s, t)) ∧
    (1 / 4 : ℝ) * (φ (xstar, ystar) + φ (xstar, t) + φ (s, ystar) + φ (s, t)) ≤
      (1 / 2 : ℝ) * φ (xstar, (1 / 2 : ℝ) • ystar + (1 / 2 : ℝ) • t) +
        (1 / 2 : ℝ) * φ (s, (1 / 2 : ℝ) • ystar + (1 / 2 : ℝ) • t) := by sorry

end BiconvexProg.Boundary
