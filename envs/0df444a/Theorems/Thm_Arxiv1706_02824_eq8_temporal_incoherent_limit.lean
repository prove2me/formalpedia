-- Prove2me | Theorems.Thm_Arxiv1706_02824_eq8_temporal_incoherent_limit
-- name    : Arxiv1706_02824.eq8_temporal_incoherent_limit
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T00:57:42.499007+00:00
-- url     : https://prove2.me/theorems/0c1eae91-8df2-4bac-b0d7-c5994f1df16e
-- title:
--   Eqs. (8) and (8'): the temporal incoherent limit $T\to\infty$
-- statement:
--   Let $w(\nu)=W_R(x_1,x_2,\nu)$ be integrable and square-integrable, and let $\mathcal S_T[w]$ be the right side of eq. (6). Then
--   $$T\,\mathcal S_T[w]\ \longrightarrow\ \int|w(\nu)|^2\,d\nu\qquad(T\to\infty),$$
--   which is eq. (8), $C_{T,R}\cong(1/T)\int|W_R|^2\,d\nu$. In particular $\mathcal S_T[w]\to0$. For cross-spectrally pure light, $w=J_R(x_1,x_2)s$ with $s\ge0$, $\int s=1$ and $s$ square-integrable,
--   $$T\,\mathcal S_T[w]\ \longrightarrow\ T_c\,|J_R(x_1,x_2)|^2,\qquad T_c=\int s^2(\nu)\,d\nu,$$
--   which is eq. (8').
--
--   **Formalization Note** The approximation for "$T$ much longer than the coherence time" is stated as the limit of $T\,C_{T,R}$ as $T\to\infty$. Square-integrability of $W_R$, which the paper leaves implicit, is what makes the right side of eq. (8) finite. The statement is about the right side of eq. (6), which equals $C_{T,R}$ by eq. (6).
-- source:
--   Gureyev, Kozlov, Paganin, Nesterets, de Hoog and Quiney, On the van Cittert - Zernike theorem for intensity correlations and its applications, arXiv:1706.02824v1 (2017), claim c029; Section 2, limit case 2, eqs. (8) and (8'), PDF pp. 2-3; the limit T -> infinity is stated in the Appendix, PDF p. 8

import Mathlib
import Definitions.Def_Arxiv1706_02824_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ComplexConjugate

namespace Arxiv1706_02824

theorem eq8_temporal_incoherent_limit (W : ℝ → ℂ) (hW : Integrable W) (hW2 : MemLp W 2) :
    Tendsto (fun T : ℝ => (T : ℂ) * sincSqIntegral W T) atTop
      (𝓝 ((∫ ν : ℝ, ‖W ν‖ ^ 2 : ℝ) : ℂ)) ∧
    Tendsto (fun T : ℝ => sincSqIntegral W T) atTop (𝓝 0) ∧
    ∀ (J : ℂ) (s : ℝ → ℝ), (∀ ν, 0 ≤ s ν) → Integrable s → MemLp s 2 → ∫ ν : ℝ, s ν = 1 →
      (∀ ν, W ν = J * (s ν : ℂ)) →
      Tendsto (fun T : ℝ => (T : ℂ) * sincSqIntegral W T) atTop
        (𝓝 ((coherenceTime s * ‖J‖ ^ 2 : ℝ) : ℂ)) := by sorry

end Arxiv1706_02824
