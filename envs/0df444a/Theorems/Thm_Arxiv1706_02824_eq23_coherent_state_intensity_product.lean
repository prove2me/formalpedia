-- Prove2me | Theorems.Thm_Arxiv1706_02824_eq23_coherent_state_intensity_product
-- name    : Arxiv1706_02824.eq23_coherent_state_intensity_product
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T01:22:53.666432+00:00
-- url     : https://prove2.me/theorems/8ac8ec70-435f-420c-af57-b65bf5f7a4fe
-- title:
--   Eq. (23): intensity-operator product in the detector plane
-- statement:
--   In the setting of eq. (22), let $c>0$, $R>0$ and $\lambda=2\pi c/\omega$. Let $u_R$ be the Fresnel transform (3) of $u_0$ over distance $R$, and $G_R(x)=E_R^-(x)E_R^+(x)$ the intensity operator built on $u_R$. Then
--   $$\langle\alpha|G_R(x_1)G_R(x_2)|\alpha\rangle=(\hbar\omega/2)^2\big(|\alpha|^4+|\alpha|^2\big)|u_R(x_1)|^2|u_R(x_2)|^2 .$$
--
--   **Formalization Note** The paper prints $\lambda=\omega/(2\pi c)$, which is dimensionally wrong; the statement uses $\lambda=2\pi c/\omega$.
-- source:
--   Gureyev, Kozlov, Paganin, Nesterets, de Hoog and Quiney, On the van Cittert - Zernike theorem for intensity correlations and its applications, arXiv:1706.02824v1 (2017), claim c032; Section 6, eq. (23), PDF p. 6

import Mathlib
import Definitions.Def_Arxiv1706_02824_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ComplexConjugate

namespace Arxiv1706_02824

theorem eq23_coherent_state_intensity_product (hbar ω : ℝ) (hhbar : 0 < hbar) (hω : 0 < ω)
    (u0 : ℝ → ℂ) (hnorm : ∫ y : ℝ, ‖u0 y‖ ^ 2 = 1) (α : ℂ) (c R : ℝ) (hc : 0 < c) (hR : 0 < R) (x1 x2 : ℝ) :
    cohExpect α (fun ψ => intensityOp hbar ω (fresnelProp (2 * π * c / ω) R u0) x1
      (intensityOp hbar ω (fresnelProp (2 * π * c / ω) R u0) x2 ψ)) =
      (((hbar * ω / 2) ^ 2 * (‖α‖ ^ 4 + ‖α‖ ^ 2) * ‖(fresnelProp (2 * π * c / ω) R u0) x1‖ ^ 2 *
        ‖(fresnelProp (2 * π * c / ω) R u0) x2‖ ^ 2 : ℝ) : ℂ) := by sorry

end Arxiv1706_02824
