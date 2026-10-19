-- Prove2me | Theorems.Thm_CauchyRiemannIndex_nonzeroLoop_homotopic_const_of_three_le_card
-- name    : CauchyRiemannIndex.nonzeroLoop_homotopic_const_of_three_le_card
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T16:49:16.884809+00:00
-- url     : https://prove2.me/theorems/e05c6cf9-d857-46b7-a6db-0c5683cf87f1
-- title:
--   Loops in $\mathbb R^m\setminus\{0\}$, $m\ge3$, are null-homotopic rel base point
-- statement:
--   Let $\iota$ be a finite set with at least three elements and let $x_0\in\mathbb R^\iota$. If $v:[0,1]\to\mathbb R^\iota\setminus\{0\}$ is continuous with $v(0)=v(1)=x_0$, then there is a continuous map $H:[0,1]\times[0,1]\to\mathbb R^\iota\setminus\{0\}$ with
--   $$H(0,t)=v(t),\qquad H(1,t)=x_0,\qquad H(s,0)=H(s,1)=x_0 .$$
--
--   That is, $\mathbb R^m\setminus\{0\}$ is simply connected for $m\ge3$, stated in the concrete form of a based null-homotopy of an arbitrary based loop. It is used for loops of vectors $t\mapsto\varphi(t)v_0$ obtained from loops $\varphi$ of matrices.
--
--   **Formalization Note.** $\mathbb R^\iota$ is the function space `ι → ℝ` with its product topology, for `[Fintype ι]` with `3 ≤ Fintype.card ι`; the loop and the homotopy are `C(unitInterval, ι → ℝ)` and `C(unitInterval × unitInterval, ι → ℝ)`, and the condition $H\neq0$ is required at every point.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, §3.4, p. 62 (auxiliary fact for Theorem 3.34: the fundamental group of $\mathrm{Sp}(2n)$)

import Definitions.Def_CauchyRiemannIndex_Setting

namespace CauchyRiemannIndex

open Matrix

/-- If `ι` has at least three elements, every loop in `ℝ^ι ∖ {0}` based at `x₀` is homotopic to
the constant loop through loops in `ℝ^ι ∖ {0}` based at `x₀`. -/
theorem nonzeroLoop_homotopic_const_of_three_le_card {ι : Type*} [Fintype ι]
    (hι : 3 ≤ Fintype.card ι) (x₀ : ι → ℝ) (v : C(unitInterval, ι → ℝ)) (hv : ∀ t, v t ≠ 0)
    (h0 : v 0 = x₀) (h1 : v 1 = x₀) :
    ∃ H : C(unitInterval × unitInterval, ι → ℝ), (∀ t, H (0, t) = v t) ∧
      (∀ t, H (1, t) = x₀) ∧ (∀ p, H p ≠ 0) ∧ (∀ s, H (s, 0) = x₀) ∧ ∀ s, H (s, 1) = x₀ := by sorry

end CauchyRiemannIndex
