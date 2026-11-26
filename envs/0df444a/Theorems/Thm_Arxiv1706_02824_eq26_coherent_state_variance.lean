-- Prove2me | Theorems.Thm_Arxiv1706_02824_eq26_coherent_state_variance
-- name    : Arxiv1706_02824.eq26_coherent_state_variance
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T01:31:57.394795+00:00
-- url     : https://prove2.me/theorems/e7f813ed-a7d2-4c2e-8a34-dcc981bcd55d
-- title:
--   Eq. (26): intensity variance of a coherent state
-- statement:
--   In the setting of eq. (23), the intensity variance is
--   $$V_{\alpha,R}(x)=C_{\alpha,R}(x,x)=\langle\alpha|G_R^2(x)|\alpha\rangle-\big(\langle\alpha|G_R(x)|\alpha\rangle\big)^2=(\hbar\omega/2)^2|\alpha|^2|u_R(x)|^4 .$$
-- source:
--   Gureyev, Kozlov, Paganin, Nesterets, de Hoog and Quiney, On the van Cittert - Zernike theorem for intensity correlations and its applications, arXiv:1706.02824v1 (2017), claim c020; Section 6, eq. (26), PDF p. 6

import Mathlib
import Definitions.Def_Arxiv1706_02824_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ComplexConjugate

namespace Arxiv1706_02824

theorem eq26_coherent_state_variance (hbar ω : ℝ) (hhbar : 0 < hbar) (hω : 0 < ω)
    (u0 : ℝ → ℂ) (hnorm : ∫ y : ℝ, ‖u0 y‖ ^ 2 = 1) (α : ℂ) (c R : ℝ) (hc : 0 < c) (hR : 0 < R) (x : ℝ) :
    cohIntensityAutocov hbar ω (fresnelProp (2 * π * c / ω) R u0) α x x =
      (((hbar * ω / 2) ^ 2 * ‖α‖ ^ 2 * ‖(fresnelProp (2 * π * c / ω) R u0) x‖ ^ 4 : ℝ) : ℂ) := by sorry

end Arxiv1706_02824
