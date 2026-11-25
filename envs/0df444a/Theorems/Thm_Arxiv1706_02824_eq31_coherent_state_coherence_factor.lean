-- Prove2me | Theorems.Thm_Arxiv1706_02824_eq31_coherent_state_coherence_factor
-- name    : Arxiv1706_02824.eq31_coherent_state_coherence_factor
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T01:50:13.329059+00:00
-- url     : https://prove2.me/theorems/83f6fc0d-cebd-5320-a286-fbd94a90e6ad
-- title:
--   Eq. (31): $\gamma_\alpha^{(2,2)}=1+|\alpha|^{-2}$ and decorrelation for large photon numbers
-- statement:
--   For a single mode with normalised mode function $u$, let $u(x_1)\ne0$ and $u(x_2)\ne0$, and let $I_\alpha(x)=\langle\alpha|G(x)|\alpha\rangle$ with $G=E^-E^+$. For every $\alpha\ne0$,
--   $$\gamma_\alpha^{(2,2)}(x_1,x_2)=\frac{\langle\alpha|G(x_1)G(x_2)|\alpha\rangle}{I_\alpha(x_1)I_\alpha(x_2)}=1+|\alpha|^{-2}.$$
--   The intensity correlation coefficient $c_\alpha^{(2,2)}=\gamma_\alpha^{(2,2)}-1$ tends to $0$ as $|\alpha|\to\infty$, i.e. as the mean photon number $\bar n=|\alpha|^2\to\infty$.
-- source:
--   Gureyev, Kozlov, Paganin, Nesterets, de Hoog and Quiney, On the van Cittert - Zernike theorem for intensity correlations and its applications, arXiv:1706.02824v1 (2017), claim c025; Section 6, eq. (31) and the following paragraph, PDF pp. 6-7

import Mathlib
import Definitions.Def_Arxiv1706_02824_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ComplexConjugate

namespace Arxiv1706_02824

theorem eq31_coherent_state_coherence_factor (hbar ω : ℝ) (hhbar : 0 < hbar) (hω : 0 < ω)
    (u0 : ℝ → ℂ) (hnorm : ∫ y : ℝ, ‖u0 y‖ ^ 2 = 1) (α : ℂ) (x1 x2 : ℝ)
    (h1 : u0 x1 ≠ 0) (h2 : u0 x2 ≠ 0) :
    (α ≠ 0 → cohGamma22 hbar ω u0 α x1 x2 = 1 + (((‖α‖ ^ 2)⁻¹ : ℝ) : ℂ)) ∧
    Tendsto (fun β : ℂ => cohGamma22 hbar ω u0 β x1 x2 - 1) (Bornology.cobounded ℂ) (𝓝 0) := by sorry

end Arxiv1706_02824
