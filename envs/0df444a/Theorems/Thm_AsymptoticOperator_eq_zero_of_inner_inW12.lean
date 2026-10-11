-- Prove2me | Theorems.Thm_AsymptoticOperator_eq_zero_of_inner_inW12
-- name    : AsymptoticOperator.eq_zero_of_inner_inW12
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T11:56:15.973365+00:00
-- url     : https://prove2.me/theorems/3dd9bf6a-e44e-49d6-9656-4ac353cab4b3
-- title:
--   $W^{1,2}(S^1,\mathbb{R}^{2n})$ has trivial orthogonal complement in $L^2(S^1,\mathbb{R}^{2n})$
-- statement:
--   Let $S^1=\mathbb R/\mathbb Z$ with its Haar probability measure and let $L^2_n=L^2(S^1,\mathbb R^{2n})$. For $f\in L^2_n$ and $k\in\mathbb Z$ let $\hat f_k=\int_{S^1}e^{-2\pi ikt}f(t)\,dt\in\mathbb C^{2n}$ be its $k$-th Fourier coefficient, computed componentwise after viewing the real entries of $f$ as complex numbers.
--
--   Say $f\in W^{1,2}$ if $\sum_{k\in\mathbb Z}(1+k^2)|\hat f_k|^2<\infty$. If $g\in L^2_n$ satisfies $\langle f,g\rangle_{L^2}=\int_{S^1}\langle f(t),g(t)\rangle\,dt=0$ for every $f\in W^{1,2}$, then $g=0$.
--
--   Equivalently, the orthogonal complement of $W^{1,2}(S^1,\mathbb R^{2n})$ in $L^2(S^1,\mathbb R^{2n})$ is zero, so every linear subspace of $L^2_n$ containing $W^{1,2}$ is dense. This is the density half of the description of the domain of the asymptotic operator $A_S=-J_0\partial_t-S$.
--
--   Formalization note: `L2 n`, `coeff` and `InW12` come from the definition module `AsymptoticOperator_Setting`; `L2 n` is `Lp (EuclideanSpace ℝ (Fin n ⊕ Fin n)) 2` over `UnitAddCircle` with `AddCircle.haarAddCircle`, `InW12 f` is the summability condition above, and `inner ℝ f g` is the $L^2$ inner product.
-- source:
--   Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, §3.2, equation (3.4)

import Definitions.Def_AsymptoticOperator_Setting

namespace AsymptoticOperator

open ConleyZehnder

/-- An element of `L²(S¹, ℝ²ⁿ)` orthogonal to every element of `W^{1,2}(S¹, ℝ²ⁿ)` is zero. -/
theorem eq_zero_of_inner_inW12 {n : ℕ} (g : L2 n)
    (h : ∀ f : L2 n, InW12 f → inner ℝ f g = 0) : g = 0 := by sorry

end AsymptoticOperator
