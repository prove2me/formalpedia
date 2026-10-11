-- Prove2me | Theorems.Thm_AsymptoticOperator_eq_zero_of_coeff_eq_zero
-- name    : AsymptoticOperator.eq_zero_of_coeff_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T11:32:41.712585+00:00
-- url     : https://prove2.me/theorems/8e484b7b-69a4-407f-80d0-ba9579e4795d
-- title:
--   An element of $L^2(S^1,\mathbb{R}^{2n})$ with vanishing Fourier coefficients is zero
-- statement:
--   Let $S^1=\mathbb R/\mathbb Z$ with its Haar probability measure and let $L^2_n=L^2(S^1,\mathbb R^{2n})$. For $f\in L^2_n$ and $k\in\mathbb Z$ let $\hat f_k=\int_{S^1}e^{-2\pi ikt}f(t)\,dt\in\mathbb C^{2n}$ be its $k$-th Fourier coefficient, computed componentwise after viewing the real entries of $f$ as complex numbers.
--
--   If $g\in L^2_n$ satisfies $\hat g_k=0$ for every $k\in\mathbb Z$, then $g=0$ in $L^2_n$.
--
--   So an element of $L^2(S^1,\mathbb R^{2n})$ is determined by its Fourier coefficients. This is the basic uniqueness statement behind every definition in this mission that specifies an element of $L^2_n$ through its Fourier coefficients, such as the asymptotic operator $A_S=-J_0\partial_t-S$.
--
--   Formalization note: `L2 n` and `coeff` come from the definition module `AsymptoticOperator_Setting`; `L2 n` is `Lp (EuclideanSpace ℝ (Fin n ⊕ Fin n)) 2` over `UnitAddCircle` with `AddCircle.haarAddCircle`, and `coeff g k` is the vector $\hat g_k$.
-- source:
--   Classical uniqueness of Fourier coefficients on L^2 of the circle (Katznelson, An Introduction to Harmonic Analysis, Chapter I, Section 2, uniqueness theorem); used for Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, §3.2, equation (3.4)

import Definitions.Def_AsymptoticOperator_Setting

namespace AsymptoticOperator

open ConleyZehnder

/-- An element of `L²(S¹, ℝ²ⁿ)` all of whose Fourier coefficients `ĝₖ ∈ ℂ²ⁿ` vanish is zero. -/
theorem eq_zero_of_coeff_eq_zero {n : ℕ} (g : L2 n) (h : ∀ k : ℤ, coeff g k = 0) :
    g = 0 := by sorry

end AsymptoticOperator
