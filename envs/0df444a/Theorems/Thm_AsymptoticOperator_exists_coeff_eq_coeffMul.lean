-- Prove2me | Theorems.Thm_AsymptoticOperator_exists_coeff_eq_coeffMul
-- name    : AsymptoticOperator.exists_coeff_eq_coeffMul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T11:56:17.011343+00:00
-- url     : https://prove2.me/theorems/593aab66-5efa-432a-ba13-f2a5bcfa7b0a
-- title:
--   Multiplication by a continuous matrix loop preserves $L^2(S^1,\mathbb{R}^{2n})$
-- statement:
--   Let $S^1=\mathbb R/\mathbb Z$ with its Haar probability measure and let $L^2_n=L^2(S^1,\mathbb R^{2n})$. For $f\in L^2_n$ and $k\in\mathbb Z$ let $\hat f_k=\int_{S^1}e^{-2\pi ikt}f(t)\,dt\in\mathbb C^{2n}$ be its $k$-th Fourier coefficient, computed componentwise after viewing the real entries of $f$ as complex numbers.
--
--   Let $S:S^1\to\mathbb R^{2n\times2n}$ be continuous (no symmetry is assumed) and $f\in L^2_n$. Then there is $m\in L^2_n$ with $\hat m_k=(Sf)^\wedge_k$ for every $k\in\mathbb Z$, where $(Sf)^\wedge_k=\int_{S^1}e^{-2\pi ikt}S(t)f(t)\,dt$.
--
--   In other words, multiplication by a continuous matrix loop maps $L^2(S^1,\mathbb R^{2n})$ into itself. This is the zeroth-order term of the asymptotic operator $A_S=-J_0\partial_t-S$.
--
--   Formalization note: `L2 n`, `coeff` and `coeffMul` come from the definition module `AsymptoticOperator_Setting`; `L2 n` is `Lp (EuclideanSpace ℝ (Fin n ⊕ Fin n)) 2` over `UnitAddCircle` with `AddCircle.haarAddCircle`, `coeff m k` is $\hat m_k$ and `coeffMul S f k` is $(Sf)^\wedge_k$, with $S(t)$ applied to the complexified vector $f(t)$.
-- source:
--   Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, §3.2, equation (3.4)

import Definitions.Def_AsymptoticOperator_Setting

namespace AsymptoticOperator

open ConleyZehnder

/-- For a continuous loop `S` of matrices and `f ∈ L²(S¹, ℝ²ⁿ)`, the product `t ↦ S(t) f(t)`
is again in `L²`: some element of `L²` has Fourier coefficients `(S f)^ₖ` for every `k`. -/
theorem exists_coeff_eq_coeffMul {n : ℕ} (S : C(UnitAddCircle, Mat n)) (f : L2 n) :
    ∃ m : L2 n, ∀ k : ℤ, coeff m k = coeffMul S f k := by sorry

end AsymptoticOperator
