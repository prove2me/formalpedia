-- Prove2me | Theorems.Thm_Arxiv1909_04681_vonMises_triple_convolution
-- name    : Arxiv1909_04681.vonMises_triple_convolution
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T06:50:59.632803+00:00
-- url     : https://prove2.me/theorems/0f6019f0-1cf0-5a2d-a419-a67269063503
-- title:
--   Eqs. (22)-(25) (as proved, normalisation corrected): the mixture distribution
-- statement:
--   Let $\mu_1,\mu_2,\mu_3\in\mathbb R$, $\kappa_1,\kappa_2,\kappa_3\ge0$, $c_0=\mu_1+\mu_2+\mu_3$, and let
--   $$G(x)=\int_0^{2\pi}\!\!\int_0^{2\pi}\mathrm{vM}(\mu_1,\kappa_1,\theta)\,\mathrm{vM}(\mu_2,\kappa_2,\phi-\theta)\,\mathrm{vM}(\mu_3,\kappa_3,x-\phi)\,d\theta\,d\phi$$
--   be the triple convolution of eq. (22). Write $\tilde G_n=\dfrac{I_n(\kappa_1)I_n(\kappa_2)I_n(\kappa_3)}{(2\pi)^3I_0(\kappa_1)I_0(\kappa_2)I_0(\kappa_3)}$ for the coefficient printed in eq. (24).
--
--   1. (Eq. 24.) For every $n\in\mathbb Z$, the Fourier coefficient $\frac1{2\pi}\int_0^{2\pi}G(x)e^{-inx}\,dx$ equals $(2\pi)^2\,\tilde G_{|n|}\,e^{-inc_0}$.
--   2. (Eq. 25.) For every $x$, the series $\sum_{n\ge1}2\tilde G_n\cos[n(x-c_0)]$ converges, and
--   $$G(x)=(2\pi)^2\Big(\frac1{(2\pi)^3}+\sum_{n=1}^\infty\frac{I_n(\kappa_1)I_n(\kappa_2)I_n(\kappa_3)\,2\cos[n(x-c_0)]}{(2\pi)^3I_0(\kappa_1)I_0(\kappa_2)I_0(\kappa_3)}\Big)=\frac1{2\pi}\Big(1+2\sum_{n=1}^\infty\prod_{i=1}^3\frac{I_n(\kappa_i)}{I_0(\kappa_i)}\cos[n(x-c_0)]\Big).$$
--
--   This closed form of the closure-phase distribution under the von Mises approximation is the paper's mixture distribution.
--
--   **Formalization Note** As printed, eqs. (24) and (25) omit the factor $(2\pi)^2$ that the convolution theorem $\widehat{(f*g)}_n=2\pi\hat f_n\hat g_n$ contributes twice; the printed right side of eq. (25) integrates to $1/(2\pi)^2$ over a period, whereas $G$ is a probability density. Eq. (24) also omits the phase $e^{-inc_0}$, which eq. (25) contains through $\cos[n(x-c_0)]$. The statement is the result of the paper's derivation carried out correctly, as is the reading $I_n(\kappa_2)$ of the twice-printed $I_n(\kappa_1)$. The concentration parameters are non-negative, as in the paper.
-- source:
--   Christian and Psaltis, Interferometric Closure Phase Uncertainties in the Low Signal-to-Noise Ratio Regime, arXiv:1909.04681v2 (2020), claim c007; Section 3, eqs. (22), (23), (24), (25), PDF p. 4

import Mathlib
import Definitions.Def_Arxiv1909_04681_Basic

open Filter Topology Asymptotics

namespace Arxiv1909_04681

theorem vonMises_triple_convolution (μ₁ μ₂ μ₃ κ₁ κ₂ κ₃ : ℝ)
    (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂) (hκ₃ : 0 ≤ κ₃) :
    (∀ n : ℤ,
      fourierCoeffOn Real.two_pi_pos (fun x => (vonMisesTripleConv μ₁ μ₂ μ₃ κ₁ κ₂ κ₃ x : ℂ)) n =
        (((2 * Real.pi) ^ 2 * mixtureFourierCoeff κ₁ κ₂ κ₃ n.natAbs : ℝ) : ℂ) *
          Complex.exp (-((n : ℂ) * ((μ₁ + μ₂ + μ₃ : ℝ) : ℂ)) * Complex.I)) ∧
    (∀ x : ℝ,
      Summable (fun n : ℕ => mixtureFourierCoeff κ₁ κ₂ κ₃ (n + 1) *
        (2 * Real.cos (((n + 1 : ℕ) : ℝ) * (x - (μ₁ + μ₂ + μ₃))))) ∧
      vonMisesTripleConv μ₁ μ₂ μ₃ κ₁ κ₂ κ₃ x = (2 * Real.pi) ^ 2 * mixtureDensity μ₁ μ₂ μ₃ κ₁ κ₂ κ₃ x) := by sorry

end Arxiv1909_04681
