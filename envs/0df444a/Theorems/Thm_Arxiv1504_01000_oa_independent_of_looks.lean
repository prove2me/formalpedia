-- Prove2me | Theorems.Thm_Arxiv1504_01000_oa_independent_of_looks
-- name    : Arxiv1504_01000.oa_independent_of_looks
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T19:02:41.741944+00:00
-- url     : https://prove2.me/theorems/562bf4d4-5b3e-4eff-bae8-5111bdfc0d31
-- title:
--   Section IV: the OA estimate does not depend on $L$
-- statement:
--   Let $[T]$ be a $3\times3$ Hermitian positive definite coherency matrix and let $L,L'>0$. The maximisers over $[-\pi/4,\pi/4]$ of $\theta\mapsto d_H(\sigma_3^2,\sigma_3^2(\theta))$ are the same for $L$ looks and for $L'$ looks. The same holds for $\theta\mapsto d_H(\sigma_2^2,\sigma_2^2(\theta))$. An angle is selected by the rule of Section III for $L$ looks if and only if it is selected for $L'$ looks. In particular, the estimated OA $\phi$, and with it $\theta_0$, does not depend on $L$.
-- source:
--   Bhattacharya, Muhuri, De, Manickam and Frery, Modifying the Yamaguchi Four-Component Decomposition Scattering Powers Using a Stochastic Distance, arXiv:1504.01000v1 (2015), claim c006 (a); Sec. IV, paragraph after eq. (12), PDF p. 5

import Mathlib
import Definitions.Def_Arxiv1504_01000_Basic

open MeasureTheory Filter Topology
open scoped ComplexOrder

namespace Arxiv1504_01000

theorem oa_independent_of_looks (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T.PosDef) (L L' : ℝ)
    (hL : 0 < L) (hL' : 0 < L') :
    (∀ θ, IsMaxOn (dH T L 2) oaRange θ ↔ IsMaxOn (dH T L' 2) oaRange θ) ∧
    (∀ θ, IsMaxOn (dH T L 1) oaRange θ ↔ IsMaxOn (dH T L' 1) oaRange θ) ∧
    (∀ φ, IsSelectedOA T L φ ↔ IsSelectedOA T L' φ) := by sorry

end Arxiv1504_01000
