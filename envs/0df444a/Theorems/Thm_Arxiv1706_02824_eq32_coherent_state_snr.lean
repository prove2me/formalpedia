-- Prove2me | Theorems.Thm_Arxiv1706_02824_eq32_coherent_state_snr
-- name    : Arxiv1706_02824.eq32_coherent_state_snr
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T01:55:56.303907+00:00
-- url     : https://prove2.me/theorems/383fb628-e841-4bcd-9fe7-881e9de4ab4e
-- title:
--   Eq. (32): $\mathrm{SNR}^2=|\alpha|^2=\bar n$ for a coherent state
-- statement:
--   In the setting of eq. (23), let $\alpha\ne0$ and $u_R(x)\ne0$. Then
--   $$\mathrm{SNR}_R^2(x)=\frac{I_{\alpha,R}^2(x)}{V_{\alpha,R}(x)}=|\alpha|^2=\bar n,$$
--   as for Poisson statistics, where $I_{\alpha,R}(x)=\langle\alpha|G_R(x)|\alpha\rangle$ and $V_{\alpha,R}$ is the variance (26).
--
--   **Formalization Note** The nonvanishing conditions, implicit in the division, are hypotheses.
-- source:
--   Gureyev, Kozlov, Paganin, Nesterets, de Hoog and Quiney, On the van Cittert - Zernike theorem for intensity correlations and its applications, arXiv:1706.02824v1 (2017), claim c026; Section 6, eq. (32), PDF p. 7

import Mathlib
import Definitions.Def_Arxiv1706_02824_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ComplexConjugate

namespace Arxiv1706_02824

theorem eq32_coherent_state_snr (hbar ω : ℝ) (hhbar : 0 < hbar) (hω : 0 < ω)
    (u0 : ℝ → ℂ) (hnorm : ∫ y : ℝ, ‖u0 y‖ ^ 2 = 1) (α : ℂ) (c R : ℝ) (hc : 0 < c) (hR : 0 < R) (x : ℝ) (hα : α ≠ 0)
    (hx : (fresnelProp (2 * π * c / ω) R u0) x ≠ 0) :
    snrSq hbar ω (fresnelProp (2 * π * c / ω) R u0) α x = ((‖α‖ ^ 2 : ℝ) : ℂ) := by sorry

end Arxiv1706_02824
