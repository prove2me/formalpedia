-- Prove2me | Theorems.Thm_AsymptoticOperator_exists_coeff_eq
-- name    : AsymptoticOperator.exists_coeff_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T11:56:11.816683+00:00
-- url     : https://prove2.me/theorems/7514394a-25d9-418c-9613-2844803086de
-- title:
--   Square-summable conjugate-symmetric sequences are Fourier coefficients of $L^2(S^1,\mathbb{R}^{2n})$ functions
-- statement:
--   Let $S^1=\mathbb R/\mathbb Z$ with its Haar probability measure and let $L^2_n=L^2(S^1,\mathbb R^{2n})$. For $f\in L^2_n$ and $k\in\mathbb Z$ let $\hat f_k=\int_{S^1}e^{-2\pi ikt}f(t)\,dt\in\mathbb C^{2n}$ be its $k$-th Fourier coefficient, computed componentwise after viewing the real entries of $f$ as complex numbers.
--
--   Let $c:\mathbb Z\to\mathbb C^{2n}$ satisfy $\sum_{k\in\mathbb Z}|c_k|^2<\infty$ and $c_{-k}=\overline{c_k}$ (componentwise) for every $k$. Then there is $h\in L^2_n$ with $\hat h_k=c_k$ for every $k\in\mathbb Z$.
--
--   Together with the uniqueness of Fourier coefficients, this identifies $L^2(S^1,\mathbb R^{2n})$ with the conjugate-symmetric square-summable sequences in $\mathbb C^{2n}$. It is used to produce elements of $L^2_n$ from prescribed Fourier coefficients, for example the image $-J_0\partial_tf$ of an element of $W^{1,2}$.
--
--   Formalization note: `L2 n` and `coeff` come from the definition module `AsymptoticOperator_Setting`; `L2 n` is `Lp (EuclideanSpace ℝ (Fin n ⊕ Fin n)) 2` over `UnitAddCircle` with `AddCircle.haarAddCircle`, and `coeff h k` is the vector $\hat h_k$. Square-summability is stated as summability of $k\mapsto\sum_i|c_k^i|^2$, and conjugate symmetry componentwise with `starRingEnd ℂ`.
-- source:
--   Riesz–Fischer theorem on the circle (Katznelson, An Introduction to Harmonic Analysis, Chapter I, Section 5); used for Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, §3.2, equation (3.4)

import Definitions.Def_AsymptoticOperator_Setting

namespace AsymptoticOperator

open ConleyZehnder

/-- Every square-summable, conjugate-symmetric family `c : ℤ → ℂ²ⁿ` is the sequence of
Fourier coefficients of an element of `L²(S¹, ℝ²ⁿ)`. -/
theorem exists_coeff_eq {n : ℕ} (c : ℤ → Fin n ⊕ Fin n → ℂ)
    (hsum : Summable fun k : ℤ => ∑ i, ‖c k i‖ ^ 2)
    (hconj : ∀ k i, c (-k) i = (starRingEnd ℂ) (c k i)) :
    ∃ h : L2 n, ∀ k : ℤ, coeff h k = c k := by sorry

end AsymptoticOperator
