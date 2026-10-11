-- Prove2me | Theorems.Thm_AsymptoticOperator_inner_mul_symm
-- name    : AsymptoticOperator.inner_mul_symm
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T16:29:55.443169+00:00
-- url     : https://prove2.me/theorems/4f773c5f-7611-4353-94a0-33220157b03c
-- title:
--   Multiplication by a loop of symmetric matrices is symmetric on $L^2(S^1,\mathbb{R}^{2n})$
-- statement:
--   Let $S^1=\mathbb R/\mathbb Z$ with its Haar probability measure and let $L^2_n=L^2(S^1,\mathbb R^{2n})$ with inner product $\langle f,g\rangle_{L^2}=\int_{S^1}\langle f(t),g(t)\rangle\,dt$. For $f\in L^2_n$ and $k\in\mathbb Z$ let $\hat f_k=\int_{S^1}e^{-2\pi ikt}f(t)\,dt\in\mathbb C^{2n}$ be its $k$-th Fourier coefficient, computed componentwise after viewing the real entries of $f$ as complex numbers.
--
--   Let $S:S^1\to\mathbb R^{2n\times2n}$ be continuous with $S(t)^{\mathsf T}=S(t)$ for every $t$. Let $f,g,m,m'\in L^2_n$ with $\hat m_k=(Sf)^\wedge_k$ and $\hat m'_k=(Sg)^\wedge_k$ for every $k\in\mathbb Z$, where $(Sf)^\wedge_k=\int_{S^1}e^{-2\pi ikt}S(t)f(t)\,dt$. Then
--   $$\langle m,g\rangle_{L^2}=\langle f,m'\rangle_{L^2}.$$
--
--   In other words, multiplication by a loop of symmetric matrices is a symmetric operator on $L^2(S^1,\mathbb R^{2n})$. This is the zeroth-order part of the symmetry of the asymptotic operator $A_S=-J_0\partial_t-S$.
--
--   Formalization note: `L2 n`, `coeff`, `coeffMul` and `IsSymLoop` come from the definition module `AsymptoticOperator_Setting`; `coeff m k` is $\hat m_k$, `coeffMul S f k` is $(Sf)^\wedge_k$ (with $S(t)$ applied to the complexified vector $f(t)$), and `inner ℝ` is the $L^2$ inner product.
-- source:
--   Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, §3.2, equation (3.4), p. 55

import Definitions.Def_AsymptoticOperator_Setting

namespace AsymptoticOperator

open ConleyZehnder

/-- For a loop `S` of symmetric matrices, multiplication by `S` is symmetric on `L²(S¹, ℝ²ⁿ)`:
if `m, m' ∈ L²` have the Fourier coefficients of `S f` and `S g`, then
`⟨m, g⟩_{L²} = ⟨f, m'⟩_{L²}`. -/
theorem inner_mul_symm {n : ℕ} (S : C(UnitAddCircle, Mat n)) (hS : IsSymLoop S)
    (f g m m' : L2 n) (hm : ∀ k : ℤ, coeff m k = coeffMul S f k)
    (hm' : ∀ k : ℤ, coeff m' k = coeffMul S g k) :
    inner ℝ m g = inner ℝ f m' := by sorry

end AsymptoticOperator
