-- Prove2me | Theorems.Thm_AsymptoticOperator_inW12_of_forall_inner
-- name    : AsymptoticOperator.inW12_of_forall_inner
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T16:58:29.054487+00:00
-- url     : https://prove2.me/theorems/e289e321-6602-447e-86ac-01ce0fb63c62
-- title:
--   Weak solutions of $-J_0\partial_t$ on $L^2(S^1,\mathbb{R}^{2n})$ lie in $W^{1,2}$
-- statement:
--   Let $S^1=\mathbb R/\mathbb Z$ with its Haar probability measure and let $L^2_n=L^2(S^1,\mathbb R^{2n})$ with inner product $\langle f,g\rangle_{L^2}=\int_{S^1}\langle f(t),g(t)\rangle\,dt$. For $f\in L^2_n$ and $k\in\mathbb Z$ let $\hat f_k=\int_{S^1}e^{-2\pi ikt}f(t)\,dt\in\mathbb C^{2n}$ be its $k$-th Fourier coefficient, computed componentwise after viewing the real entries of $f$ as complex numbers. Let $W^{1,2}=\{f\in L^2_n:\sum_k(1+k^2)|\hat f_k|^2<\infty\}$ and let $J_0=\begin{pmatrix}0&-I\\ I&0\end{pmatrix}$.
--
--   Let $g,u\in L^2_n$. Suppose that for every $f\in W^{1,2}$ and every $p\in L^2_n$ with $\hat p_k=-2\pi ik\,J_0\hat f_k$ for all $k$ (that is, $p=-J_0f'$),
--   $$\langle p,g\rangle_{L^2}=\langle f,u\rangle_{L^2}.$$
--   Then $g\in W^{1,2}$ and $\hat u_k=-2\pi ik\,J_0\hat g_k$ for every $k\in\mathbb Z$, that is, $u=-J_0g'$.
--
--   In other words, the operator $-J_0\partial_t$ with domain $W^{1,2}$ is self-adjoint on $L^2(S^1,\mathbb R^{2n})$: every weak solution of $-J_0g'=u$ with $g,u\in L^2$ is a strong one. This is the first-order part of the self-adjointness of the asymptotic operator $A_S=-J_0\partial_t-S$.
--
--   Formalization note: `L2 n`, `coeff` and `InW12` come from the definition module `AsymptoticOperator_Setting`; `coeff f k` is $\hat f_k$, `InW12 f` means $f\in W^{1,2}$, `J₀ n` is $J_0$ (mapped entrywise into $\mathbb C$), and `inner ℝ` is the $L^2$ inner product.
-- source:
--   Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, §3.2, equation (3.4), p. 55; Hofer-Wysocki-Zehnder (GAFA 1995), §3

import Definitions.Def_AsymptoticOperator_Setting

namespace AsymptoticOperator

open Matrix ConleyZehnder

/-- Weak solutions of `-J₀ ∂ₜ` on the circle are strong: if `g, u ∈ L²(S¹, ℝ²ⁿ)` satisfy
`⟨-J₀ f', g⟩_{L²} = ⟨f, u⟩_{L²}` for every `f ∈ W^{1,2}(S¹, ℝ²ⁿ)` (with `p = -J₀ f'` given by
its Fourier coefficients `p̂ₖ = -2πik J₀ f̂ₖ`), then `g ∈ W^{1,2}` and `u = -J₀ g'`. -/
theorem inW12_of_forall_inner {n : ℕ} (g u : L2 n)
    (h : ∀ f p : L2 n, InW12 f →
      (∀ k : ℤ, coeff p k =
        -((2 * Real.pi * k : ℝ) * Complex.I) • ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ coeff f k)) →
      inner ℝ p g = inner ℝ f u) :
    InW12 g ∧ ∀ k : ℤ, coeff u k =
      -((2 * Real.pi * k : ℝ) * Complex.I) • ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ coeff g k) := by
  sorry

end AsymptoticOperator
