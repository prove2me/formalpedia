-- Prove2me | Theorems.Thm_DiscreteConvex_CombinatorialB_prop_2_13_farkas_lemma_equality_form
-- name    : DiscreteConvex.CombinatorialB.prop_2_13_farkas_lemma_equality_form
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T21:31:50.120277+00:00
-- url     : https://prove2.me/theorems/b6ce516e-99ee-4f22-80b8-af09e439f6b0
-- title:
--   Proposition 2.13 -- the Farkas lemma (equality form) and its nonsingular strict variant
-- statement:
--   For a matrix $A$ and vector $b$: $Ax=b$ has a nonnegative solution iff $y^\top b\ge0$ for every $y$ with $y^\top A\ge0$; if $A$ is nonsingular, this is further equivalent to $y^\top b\ge0$ for every $y$ with $y^\top A>0$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.71-72, Proposition 2.13.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.71-72, Proposition 2.13

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, pp.71-72, Proposition 2.13, in
`DiscreteConvex.CombinatorialB`.
-/

namespace DiscreteConvex.CombinatorialB

/-- **Proposition 2.13** (the Farkas lemma, equality form, plus the nonsingular strict
variant). For a matrix `A` and a vector `b`: (a) `Ax = b` for some `x ≥ 0` is equivalent to
(b) `y⊤b ≥ 0` for every `y` with `y⊤A ≥ 0`. If `A` is nonsingular, (b) is further equivalent to
(c) `y⊤b ≥ 0` for every `y` with `y⊤A > 0`. -/
theorem prop_2_13_farkas_lemma_equality_form {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (b : V → ℝ) :
    ((∃ x : V → ℝ, (∀ j, 0 ≤ x j) ∧ A.mulVec x = b) ↔
      (∀ y : V → ℝ, (∀ j, 0 ≤ Matrix.vecMul y A j) → 0 ≤ dotProduct y b)) ∧
    (A.det ≠ 0 →
      ((∀ y : V → ℝ, (∀ j, 0 ≤ Matrix.vecMul y A j) → 0 ≤ dotProduct y b) ↔
        (∀ y : V → ℝ, (∀ j, 0 < Matrix.vecMul y A j) → 0 ≤ dotProduct y b))) := by sorry

end DiscreteConvex.CombinatorialB
