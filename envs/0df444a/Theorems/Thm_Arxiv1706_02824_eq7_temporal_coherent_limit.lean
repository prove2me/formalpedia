-- Prove2me | Theorems.Thm_Arxiv1706_02824_eq7_temporal_coherent_limit
-- name    : Arxiv1706_02824.eq7_temporal_coherent_limit
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T00:52:57.744015+00:00
-- url     : https://prove2.me/theorems/6160a3d5-9d07-4dc4-877a-8fd3f7bc3dbb
-- title:
--   Eq. (7): the temporal coherent limit $T\to0$
-- statement:
--   Let $w(\nu)=W_R(x_1,x_2,\nu)$ be integrable. Then the right side of eq. (6) satisfies
--   $$\iint w(\nu_1)w^*(\nu_2)\,\mathrm{sinc}^2[\pi(\nu_1-\nu_2)T]\,d\nu_1d\nu_2\ \longrightarrow\ \Big|\int w(\nu)\,d\nu\Big|^2\qquad(T\to0^+),$$
--   which is eq. (7), $C_{T,R}(x_1,x_2)\cong|\int W_R(x_1,x_2,\nu)\,d\nu|^2$. For cross-spectrally pure light, $w(\nu)=J_R(x_1,x_2)s(\nu)$ with $s\ge0$ and $\int s=1$, the limit is $|J_R(x_1,x_2)|^2$, which is eq. (5).
--
--   **Formalization Note** The approximation "$T$ so short that $\mathrm{sinc}^2\cong1$ over the support of $W_R$" is stated as the limit $T\to0^+$, the form the Appendix gives. The statement is about the right side of eq. (6), which equals $C_{T,R}(x_1,x_2)$ by eq. (6).
-- source:
--   Gureyev, Kozlov, Paganin, Nesterets, de Hoog and Quiney, On the van Cittert - Zernike theorem for intensity correlations and its applications, arXiv:1706.02824v1 (2017), claim c002; Section 2, limit case 1, eq. (7), PDF p. 2; the limit T -> 0 is stated in the Appendix, PDF p. 8

import Mathlib
import Definitions.Def_Arxiv1706_02824_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ComplexConjugate

namespace Arxiv1706_02824

theorem eq7_temporal_coherent_limit (W : ℝ → ℂ) (hW : Integrable W) :
    Tendsto (fun T : ℝ => sincSqIntegral W T) (𝓝[>] 0) (𝓝 ((‖∫ ν : ℝ, W ν‖ ^ 2 : ℝ) : ℂ)) ∧
    ∀ (J : ℂ) (s : ℝ → ℝ), (∀ ν, 0 ≤ s ν) → Integrable s → ∫ ν : ℝ, s ν = 1 →
      (∀ ν, W ν = J * (s ν : ℂ)) →
      Tendsto (fun T : ℝ => sincSqIntegral W T) (𝓝[>] 0) (𝓝 ((‖J‖ ^ 2 : ℝ) : ℂ)) := by sorry

end Arxiv1706_02824
