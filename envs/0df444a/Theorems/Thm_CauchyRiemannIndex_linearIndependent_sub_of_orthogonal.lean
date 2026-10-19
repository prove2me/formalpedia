-- Prove2me | Theorems.Thm_CauchyRiemannIndex_linearIndependent_sub_of_orthogonal
-- name    : CauchyRiemannIndex.linearIndependent_sub_of_orthogonal
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T14:02:27.596816+00:00
-- url     : https://prove2.me/theorems/0a3842d1-b8ae-4363-9ee3-ef9eef4ca581
-- title:
--   Small perturbations of an orthogonal family are linearly independent
-- statement:
--   Let $H$ be a real inner product space, $\iota$ a finite index set, and $V,W:\iota\to H$. Suppose that $\langle V_i,V_j\rangle=0$ for $i\ne j$, that $\|V_i\|^2\ge L$ and $\|W_i\|\le\varepsilon$ for all $i$, and that
--   $$(\#\iota)^2\,\varepsilon^2<L .$$
--   Then the vectors $V_i-W_i$, $i\in\iota$, are linearly independent.
--
--   **Formalization Note.** The conclusion is `LinearIndependent ℝ (fun i => V i - W i)`; $\#\iota$ is `Fintype.card ι`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 5, proof of Proposition 5.24, p. 100

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs

namespace CauchyRiemannIndex

open scoped RealInnerProductSpace

/-- In a real inner product space, let `V : ι → H` be a finite family of pairwise orthogonal
vectors with `‖V i‖² ≥ L` and let `W : ι → H` satisfy `‖W i‖ ≤ ε`. If `(#ι)² ε² < L`, then the
family `V i - W i` is linearly independent. -/
theorem linearIndependent_sub_of_orthogonal {ι H : Type*} [Fintype ι] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (V W : ι → H) (L ε : ℝ) (hVV : ∀ i j, i ≠ j → ⟪V j, V i⟫ = 0)
    (hVn : ∀ i, L ≤ ‖V i‖ ^ 2) (hW : ∀ i, ‖W i‖ ≤ ε)
    (hsmall : (Fintype.card ι : ℝ) ^ 2 * ε ^ 2 < L) :
    LinearIndependent ℝ fun i => V i - W i := by
  sorry

end CauchyRiemannIndex
