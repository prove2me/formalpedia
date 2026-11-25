-- Prove2me | Theorems.Thm_Arxiv1510_02920_tanh_profile_no_gain
-- name    : Arxiv1510_02920.tanh_profile_no_gain
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T02:10:56.078517+00:00
-- url     : https://prove2.me/theorems/02d8c094-2cee-4509-9b61-9098f8a0cd30
-- title:
--   Eq. (8): the profile (8) has no gain at any frequency when $\gamma$ is not too small
-- statement:
--   Let $c>0$, $a>0$, $\Omega\ne0$, and let $\varepsilon_\gamma$ be the permittivity (3) with $P$ from (4) and $f$ from (8). Then there is $\gamma_0$ such that for every $\gamma\ge\gamma_0$,
--
--   $$\operatorname{Im}\varepsilon_\gamma(x,\omega)>0\qquad\text{for all }x\in\mathbb{R}\text{ and all }\omega>0.$$
--
--   **Formalization Note** "If $\gamma$ is not too small" is read as "for all sufficiently large $\gamma$"; the paper gives no threshold. The hypothesis $\Omega\ne0$ is implicit in the paper: for $\Omega=0$ the medium is vacuum and $\operatorname{Im}\varepsilon=0$.
-- source:
--   T. G. Philbin, All-frequency reflectionlessness, arXiv:1510.02920v1 (2015), claim c006; unnumbered main text, sentence after eq. (8), PDF p. 4

import Mathlib
import Definitions.Def_Arxiv1510_02920_Basic

open Filter Topology Asymptotics

namespace Arxiv1510_02920

theorem tanh_profile_no_gain (c a Om : ℝ) (hc : 0 < c) (ha : 0 < a) (hOm : Om ≠ 0) :
    ∀ᶠ γ in atTop, CondNoGain (tanhPerm c Om a γ) := by sorry

end Arxiv1510_02920
