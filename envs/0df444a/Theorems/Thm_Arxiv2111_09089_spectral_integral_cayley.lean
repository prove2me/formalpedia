-- Prove2me | Theorems.Thm_Arxiv2111_09089_spectral_integral_cayley
-- name    : Arxiv2111_09089.spectral_integral_cayley
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T10:34:19.05355+00:00
-- url     : https://prove2.me/theorems/c942b1af-261a-5608-a99f-75c297442a7a
-- title:
--   Eq. (4): the spectral integral as an integral over the unit circle (as corrected)
-- statement:
--   Let $\alpha>0$ and let $F:\mathbb C\to\mathbb C$ be a function, standing for the integrand $g(\xi;z,z')H_n^{(2)}(k\xi\rho)$ of eq. (1). Suppose $\mu\mapsto F((1+j\alpha)\mu)$ is integrable on $\mathbb R$. Then the integral along the tilted path $\xi=(1+j\alpha)\mu$ of eq. (2) equals an integral over the unit circle $C_1$ in the Cayley variable $\eta$, $\mu=-j(1+\eta)/(1-\eta)$:
--
--   $$\int_{-\infty}^{\infty}(1+j\alpha)\,F\big((1+j\alpha)\mu\big)\,d\mu=\oint_{C_1}(1+j\alpha)\,\frac{2j}{(1-\eta)^2}\,F\big((1+j\alpha)\mu(\eta)\big)\,d\eta,$$
--
--   where $C_1$ is traversed counter-clockwise.
--
--   **Formalization Note** Eq. (4) prints the kernel $(1+j\alpha)\,\frac{-j}{(1-\eta)^2}\,g$ and leaves the orientation of $C_1$ unstated. The Jacobian of eq. (3) is $-2j/(1-\eta)^2$ (see the previous statement). As $\mu$ runs from $-\infty$ to $\infty$, $\eta$ runs clockwise around $C_1$. Together these give the kernel $2j/(1-\eta)^2$ for the counter-clockwise integral, which is $-2$ times the printed one. The identity is stated for every integrand $F$ for which the left side exists. The left side is eq. (1) after the substitution of eq. (2); the equality of eqs. (1) and (2) (claim c002) is not part of this statement.
-- source:
--   Y. Hadad, On the use of the Padé-Fourier approximation in fast evaluation of the Green's function of layered media, arXiv:2111.09089v1 (2021), claim c003; Section II-B eq. (2) and Section II-C eqs. (3)-(4), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv2111_09089_Basic

open Complex MeasureTheory Filter Topology Asymptotics

namespace Arxiv2111_09089

theorem spectral_integral_cayley (α : ℝ) (hα : 0 < α) (F : ℂ → ℂ)
    (hF : Integrable (fun μ : ℝ => F (xiOfMu α μ))) :
    ∫ μ : ℝ, (1 + α * I) * F (xiOfMu α μ) =
      ∮ η in C(0, 1), (1 + α * I) * (2 * I / (1 - η) ^ 2) * F (xiOfMu α (cayley η)) := by sorry

end Arxiv2111_09089
