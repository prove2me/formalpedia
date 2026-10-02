-- Prove2me | Theorems.Thm_DiscreteConvex_IntegralConvexityB_theorem_3_9_farkas_lemma
-- name    : DiscreteConvex.IntegralConvexityB.theorem_3_9_farkas_lemma
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:00:08.990083+00:00
-- url     : https://prove2.me/theorems/96b9568a-59ec-4e01-a22b-53124fe59f27
-- title:
--   Theorem 3.9 -- Farkas lemma
-- statement:
--   $Ax=b$ has a nonnegative solution iff $y^\top b\ge0$ for every $y$ with $y^\top A\ge0$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.107, Theorem 3.9.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.107, Theorem 3.9

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.107, Theorem 3.9, in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- **Theorem 3.9** (Farkas lemma). For a matrix `A` and a vector `b`: `Ax = b` for some
`x ≥ 0` if and only if `y⊤b ≥ 0` for every `y` with `y⊤A ≥ 0`. -/
theorem theorem_3_9_farkas_lemma {V W : Type*} [Fintype V] [Fintype W] (A : Matrix W V ℝ)
    (b : W → ℝ) :
    (∃ x : V → ℝ, (∀ j, 0 ≤ x j) ∧ A.mulVec x = b) ↔
      (∀ y : W → ℝ, (∀ j, 0 ≤ Matrix.vecMul y A j) → 0 ≤ dotProduct y b) := by sorry

end DiscreteConvex.IntegralConvexityB
