-- Prove2me | Theorems.Thm_AsymptoticOperator_hasDerivAt_iff_coeff
-- name    : AsymptoticOperator.hasDerivAt_iff_coeff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T23:58:42.563988+00:00
-- url     : https://prove2.me/theorems/172ba2a2-31e1-481f-9a8e-2e6fc0eb9f67
-- title:
--   Derivatives of continuous loops in terms of Fourier coefficients
-- statement:
--   Let $\varphi,h:S^1\to\mathbb{R}^{2n}$ be continuous, $S^1=\mathbb{R}/\mathbb{Z}$, and regard them as $1$-periodic functions on $\mathbb{R}$. With Fourier coefficients $\hat g_k=\int_{S^1}e^{-2\pi i k t}g(t)\,dt\in\mathbb{C}^{2n}$ (Haar probability measure), the following are equivalent:
--
--   1. $t\mapsto\varphi(t)$ is differentiable at every $t\in\mathbb{R}$ with derivative $h(t)$;
--   2. $\hat h_k=2\pi i k\,\hat\varphi_k$ for every $k\in\mathbb{Z}$.
--
--   This identifies classical derivatives of continuous loops with the Fourier-side derivative $\hat f_k\mapsto 2\pi i k\,\hat f_k$ that defines the asymptotic operator $A_S=-J_0\partial_t-S$ on $W^{1,2}(S^1,\mathbb{R}^{2n})$, in both directions: continuous solutions of the Fourier-side equation are classical solutions, and classical periodic solutions satisfy it.
--
--   **Formalization Note.** `φ h : C(UnitAddCircle, Vec n)` with `Vec n = EuclideanSpace ℝ (Fin n ⊕ Fin n)`; condition 1 is `∀ x : ℝ, HasDerivAt (fun y : ℝ => φ ↑y) (h ↑x) x`; condition 2 is `∀ k : ℤ, coeff h k = ((2 * π * k : ℝ) * I) • coeff φ k`, with `coeff` the componentwise `fourierCoeff` of the complexification (setting module).
-- source:
--   Auxiliary statement for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 3, §3.4 p. 61 (kernel of the asymptotic operator)

import Definitions.Def_AsymptoticOperator_Setting

namespace AsymptoticOperator

/-- For continuous loops `φ, h : S¹ → ℝ²ⁿ`, `h` is the classical derivative of `φ` (viewed as a
`1`-periodic function on `ℝ`) if and only if `ĥₖ = 2πik φ̂ₖ` for every `k ∈ ℤ`. -/
theorem hasDerivAt_iff_coeff {n : ℕ} (φ h : C(UnitAddCircle, Vec n)) :
    (∀ x : ℝ, HasDerivAt (fun y : ℝ => φ (y : UnitAddCircle)) (h (x : UnitAddCircle)) x) ↔
      ∀ k : ℤ, coeff h k = ((2 * Real.pi * k : ℝ) * Complex.I) • coeff φ k := by
  sorry

end AsymptoticOperator
