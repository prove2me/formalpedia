-- Prove2me | Theorems.Thm_Arxiv1706_02824_eq27_coherent_state_far_field
-- name    : Arxiv1706_02824.eq27_coherent_state_far_field
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T01:36:26.947002+00:00
-- url     : https://prove2.me/theorems/1d3d8e74-c15c-4bc9-8f6f-ca0d3a3c64d3
-- title:
--   Eq. (27): far-field intensity autocovariance of a coherent state
-- statement:
--   In the setting of eq. (22), let $u_0$ be integrable, $c>0$ and $\lambda=2\pi c/\omega$. Let $u_R$ be the Fresnel transform of $u_0$ and $C_{\alpha,R}$ the autocovariance (25). Then for all $\xi_1,\xi_2$,
--   $$(\lambda R)^2\,C_{\alpha,R}(\lambda R\xi_1,\lambda R\xi_2)\ \longrightarrow\ (\hbar\omega/2)^2|\alpha|^2\,|\hat u_0(\xi_1)|^2|\hat u_0(\xi_2)|^2\qquad(R\to\infty).$$
--   That is, for large $R$,
--   $$C_{\alpha,R}(x_1,x_2)\cong\frac{(\hbar\omega/2)^2|\alpha|^2}{(\lambda R)^2}\Big|\hat u_0\Big(\frac{x_1}{\lambda R}\Big)\Big|^2\Big|\hat u_0\Big(\frac{x_2}{\lambda R}\Big)\Big|^2 .$$
--
--   This is the coherent-state analogue of the vCZ2 theorem (11).
--
--   **Formalization Note** "For sufficiently large $R$ the Fresnel integrals can be replaced by Fourier transforms" is stated as the limit $R\to\infty$ at fixed scaled coordinates $\xi_i=x_i/(\lambda R)$. Integrability of $u_0$ is assumed so that the Fresnel integral converges absolutely.
-- source:
--   Gureyev, Kozlov, Paganin, Nesterets, de Hoog and Quiney, On the van Cittert - Zernike theorem for intensity correlations and its applications, arXiv:1706.02824v1 (2017), claim c021; Section 6, eq. (27) and the sentence before it, PDF p. 6

import Mathlib
import Definitions.Def_Arxiv1706_02824_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ComplexConjugate

namespace Arxiv1706_02824

theorem eq27_coherent_state_far_field (hbar ω : ℝ) (hhbar : 0 < hbar) (hω : 0 < ω)
    (u0 : ℝ → ℂ) (hnorm : ∫ y : ℝ, ‖u0 y‖ ^ 2 = 1) (α : ℂ) (c : ℝ) (hc : 0 < c)
    (hu0 : Integrable u0) (ξ1 ξ2 : ℝ) :
    Tendsto (fun R : ℝ => (((2 * π * c / ω * R) ^ 2 : ℝ) : ℂ) *
        cohIntensityAutocov hbar ω (fresnelProp (2 * π * c / ω) R u0) α
          (2 * π * c / ω * R * ξ1) (2 * π * c / ω * R * ξ2)) atTop
      (𝓝 (((hbar * ω / 2) ^ 2 * ‖α‖ ^ 2 * ‖ft u0 ξ1‖ ^ 2 * ‖ft u0 ξ2‖ ^ 2 : ℝ) : ℂ)) := by sorry

end Arxiv1706_02824
