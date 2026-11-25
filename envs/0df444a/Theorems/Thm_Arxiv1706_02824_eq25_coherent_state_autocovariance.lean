-- Prove2me | Theorems.Thm_Arxiv1706_02824_eq25_coherent_state_autocovariance
-- name    : Arxiv1706_02824.eq25_coherent_state_autocovariance
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T01:27:25.497022+00:00
-- url     : https://prove2.me/theorems/f9dd175b-be51-4d16-8d9c-0e5badaaebc8
-- title:
--   Eqs. (24)-(25): mean intensity and intensity autocovariance of a coherent state
-- statement:
--   In the setting of eq. (23), for every $x$,
--   $$\langle\alpha|G_R(x)|\alpha\rangle=(\hbar\omega/2)|\alpha|^2|u_R(x)|^2\qquad(24),$$
--   and the intensity autocovariance is
--   $$C_{\alpha,R}(x_1,x_2)=\langle\alpha|G_R(x_1)G_R(x_2)|\alpha\rangle-\langle\alpha|G_R(x_1)|\alpha\rangle\langle\alpha|G_R(x_2)|\alpha\rangle=(\hbar\omega/2)^2|\alpha|^2|u_R(x_1)|^2|u_R(x_2)|^2\qquad(25).$$
--
--   The autocovariance is proportional to the mean photon number $\bar n=|\alpha|^2$, as for Poisson statistics.
-- source:
--   Gureyev, Kozlov, Paganin, Nesterets, de Hoog and Quiney, On the van Cittert - Zernike theorem for intensity correlations and its applications, arXiv:1706.02824v1 (2017), claim c019; Section 6, eqs. (24)-(25), PDF p. 6

import Mathlib
import Definitions.Def_Arxiv1706_02824_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ComplexConjugate

namespace Arxiv1706_02824

theorem eq25_coherent_state_autocovariance (hbar ω : ℝ) (hhbar : 0 < hbar) (hω : 0 < ω)
    (u0 : ℝ → ℂ) (hnorm : ∫ y : ℝ, ‖u0 y‖ ^ 2 = 1) (α : ℂ) (c R : ℝ) (hc : 0 < c) (hR : 0 < R) (x1 x2 : ℝ) :
    (∀ x : ℝ, cohExpect α (intensityOp hbar ω (fresnelProp (2 * π * c / ω) R u0) x) =
      ((hbar * ω / 2 * ‖α‖ ^ 2 * ‖(fresnelProp (2 * π * c / ω) R u0) x‖ ^ 2 : ℝ) : ℂ)) ∧
    cohIntensityAutocov hbar ω (fresnelProp (2 * π * c / ω) R u0) α x1 x2 =
      (((hbar * ω / 2) ^ 2 * ‖α‖ ^ 2 * ‖(fresnelProp (2 * π * c / ω) R u0) x1‖ ^ 2 *
        ‖(fresnelProp (2 * π * c / ω) R u0) x2‖ ^ 2 : ℝ) : ℂ) := by sorry

end Arxiv1706_02824
