-- Prove2me | Theorems.Thm_AsymptoticOperator_hasSum_inner_coeff
-- name    : AsymptoticOperator.hasSum_inner_coeff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T16:27:02.021996+00:00
-- url     : https://prove2.me/theorems/768138ce-f509-4dcb-b28d-9b89e73a2494
-- title:
--   Parseval's identity on $L^2(S^1,\mathbb{R}^{2n})$
-- statement:
--   Let $S^1=\mathbb R/\mathbb Z$ with its Haar probability measure and let $L^2_n=L^2(S^1,\mathbb R^{2n})$ with inner product $\langle f,g\rangle_{L^2}=\int_{S^1}\langle f(t),g(t)\rangle\,dt$. For $f\in L^2_n$ and $k\in\mathbb Z$ let $\hat f_k=\int_{S^1}e^{-2\pi ikt}f(t)\,dt\in\mathbb C^{2n}$ be its $k$-th Fourier coefficient, computed componentwise after viewing the real entries of $f$ as complex numbers.
--
--   For all $f,g\in L^2_n$,
--   $$\langle f,g\rangle_{L^2}=\sum_{k\in\mathbb Z}\operatorname{Re}\sum_{i}\overline{(\hat f_k)_i}\,(\hat g_k)_i,$$
--   the series converging (unconditionally) to the left-hand side, where $i$ runs over the $2n$ coordinates.
--
--   This is Parseval's identity for $\mathbb R^{2n}$-valued functions on the circle. It expresses $L^2$ inner products, such as those appearing in the symmetry of the asymptotic operator $A_S=-J_0\partial_t-S$, in terms of Fourier coefficients.
--
--   Formalization note: `L2 n` and `coeff` come from the definition module `AsymptoticOperator_Setting`; `L2 n` is `Lp (EuclideanSpace ℝ (Fin n ⊕ Fin n)) 2` over `UnitAddCircle` with `AddCircle.haarAddCircle`, `coeff f k` is $\hat f_k$, and `inner ℝ f g` is the $L^2$ inner product. The identity is stated as `HasSum` over $k\in\mathbb Z$.
-- source:
--   Parseval's identity on the circle (Katznelson, An Introduction to Harmonic Analysis, Chapter I, Section 5); used for Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, §3.2, equation (3.4)

import Definitions.Def_AsymptoticOperator_Setting

namespace AsymptoticOperator

open ConleyZehnder

/-- Parseval's identity on `L²(S¹, ℝ²ⁿ)`: `⟨f, g⟩_{L²} = ∑ₖ Re ⟨f̂ₖ, ĝₖ⟩_{ℂ²ⁿ}`. -/
theorem hasSum_inner_coeff {n : ℕ} (f g : L2 n) :
    HasSum (fun k : ℤ => (∑ i, (starRingEnd ℂ) (coeff f k i) * coeff g k i).re)
      (inner ℝ f g) := by sorry

end AsymptoticOperator
