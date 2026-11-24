-- Prove2me | Theorems.Thm_Arxiv1504_01000_relative_hellinger_unimodal_in_looks
-- name    : Arxiv1504_01000.relative_hellinger_unimodal_in_looks
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T19:18:51.371777+00:00
-- url     : https://prove2.me/theorems/5c79aaf7-99af-4f2b-a075-305dc24f3e0a
-- title:
--   Section IV, Fig. 3: $\delta_H$ rises with $L$ to a maximum $\delta_H^m$ at $L_m$, then decreases to zero
-- statement:
--   Let $[T]$ be a $3\times3$ Hermitian positive definite coherency matrix, and let $\phi$ be an orientation angle selected by the rule of Section III, for some number of looks $L_0>0$. Consider the relative Hellinger distance $\delta_H(L)=d_H(\sigma_3^2,\sigma_3^2(\phi))-d_H(\sigma_2^2,\sigma_2^2(\phi))$ as a function of $L>0$. There is an $L_m>0$ such that
--
--   1. $\delta_H$ is strictly increasing on $(0,L_m]$;
--   2. $\delta_H$ is strictly decreasing on $[L_m,\infty)$;
--   3. $\delta_H(L)\to0$ as $L\to\infty$;
--   4. $\delta_H(L_m)=\delta_H^m=\sup_{L>0}\delta_H(L)$, the maximum attainable relative distance with which the Y4O powers are modified.
--
--   **Formalization Note** The number of looks is a continuous variable $L>0$, as in Fig. 3. The paper's "rapidly decreases to zero" is stated as strict decrease on $[L_m,\infty)$ together with the limit $0$; the word "rapidly" is not formalised.
-- source:
--   Bhattacharya, Muhuri, De, Manickam and Frery, Modifying the Yamaguchi Four-Component Decomposition Scattering Powers Using a Stochastic Distance, arXiv:1504.01000v1 (2015), claim c006 (b), (c); Sec. IV, paragraph after eq. (12) and Fig. 3, PDF p. 5

import Mathlib
import Definitions.Def_Arxiv1504_01000_Basic

open MeasureTheory Filter Topology
open scoped ComplexOrder

namespace Arxiv1504_01000

theorem relative_hellinger_unimodal_in_looks (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T.PosDef)
    (L₀ : ℝ) (hL₀ : 0 < L₀) (φ : ℝ) (hφ : IsSelectedOA T L₀ φ) :
    ∃ Lm : ℝ, 0 < Lm ∧
      StrictMonoOn (fun L => deltaH T L φ) (Set.Ioc 0 Lm) ∧
      StrictAntiOn (fun L => deltaH T L φ) (Set.Ici Lm) ∧
      Tendsto (fun L => deltaH T L φ) atTop (𝓝 0) ∧
      deltaHm T φ = deltaH T Lm φ := by sorry

end Arxiv1504_01000
