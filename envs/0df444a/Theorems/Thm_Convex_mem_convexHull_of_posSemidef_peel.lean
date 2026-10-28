-- Prove2me | Theorems.Thm_Convex_mem_convexHull_of_posSemidef_peel
-- name    : Convex.mem_convexHull_of_posSemidef_peel
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T05:15:03.298896+00:00
-- url     : https://prove2.me/theorems/10aebccd-4c4e-4cec-805f-0d01730ed4db
-- title:
--   Peeling a positive semidefinite matrix one rank-one term at a time lands in a convex hull
-- statement:
--   Let $E$ be a real vector space, let $\iota$ be a finite index type, let $D \subseteq E$, and let
--   $\Phi(p, Z)$ be a predicate on pairs of a point $p \in E$ and a matrix
--   $Z \in \mathbb{R}^{\iota \times \iota}$. Suppose
--
--   1. base case: $\Phi(p, 0)$ implies $p \in D$;
--   2. peeling step: whenever $Z$ is positive semidefinite, $z \in \mathbb{R}^{\iota}$ and
--      $\Phi(p,\, Z + z z^{\mathsf T})$ holds, the point $p$ splits as a midpoint
--      $p = \tfrac{1}{2} p_1 + \tfrac{1}{2} p_2$ with $\Phi(p_1, Z)$ and $\Phi(p_2, Z)$.
--
--   Then for every positive semidefinite $Z$ and every $p$ with $\Phi(p, Z)$,
--
--   $$
--   p \in \operatorname{conv}(D) .
--   $$
--
--   This packages the induction that recurs throughout semidefinite rank reduction: strip one
--   rank-one term off the matrix, split the point into a midpoint of two points satisfying the
--   weaker condition, and repeat until the matrix is zero. Writing it once as a statement about an
--   abstract predicate means a formalization that needs the conclusion -- a worst-case distribution
--   lies in the convex hull of the discrete ones, for instance -- supplies two short steps instead of
--   redoing the recursion.
-- source:
--   S. Zymler, D. Kuhn and B. Rustem, Distributionally robust joint chance constraints with second-order moment information, Mathematical Programming 137 (2013), 167-198. Carved from https://prove2.me/submissions/3c55ced4-4944-4de2-ba43-8110d2682db1, lines 1645-1665 (the goal proof of DRJointCC.Joint.theorem_3_6, which re-derives it inline; the same block appears in https://prove2.me/submissions/351d29f4-df20-4118-a8bc-25a1b62a5233 for DRJointCC.Individual.theorem_2_2)

import Mathlib

open Matrix

theorem Convex.mem_convexHull_of_posSemidef_peel {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι] (D : Set E) (Φ : E → Matrix ι ι ℝ → Prop)
    (base : ∀ p, Φ p 0 → p ∈ D)
    (step : ∀ p (Z : Matrix ι ι ℝ) (z : ι → ℝ), Z.PosSemidef → Φ p (Z + vecMulVec z z) →
      ∃ p₁ p₂, p = (1 / 2 : ℝ) • p₁ + (1 / 2 : ℝ) • p₂ ∧ Φ p₁ Z ∧ Φ p₂ Z)
    {p : E} {Z : Matrix ι ι ℝ} (hZ : Z.PosSemidef) (hp : Φ p Z) :
    p ∈ convexHull ℝ D := by sorry
