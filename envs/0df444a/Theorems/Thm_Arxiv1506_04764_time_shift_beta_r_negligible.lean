-- Prove2me | Theorems.Thm_Arxiv1506_04764_time_shift_beta_r_negligible
-- name    : Arxiv1506_04764.time_shift_beta_r_negligible
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T14:37:32.792961+00:00
-- url     : https://prove2.me/theorems/a01019b8-3507-42e4-8609-ad209c92977a
-- title:
--   Sec. 2.2: the time shift β·r'/c compared with β²t'
-- statement:
--   Let the satellite move along the $x$-axis with speed $0<v_s<c$, so that $\beta=(v_s/c,0,0)$ and $\beta=|\beta|=v_s/c$, and let an antenna sit at $r'=(x',y',h)$ in the satellite frame. Then for every $t'>0$
--
--   $$\Big|\frac{\beta\cdot r'}{c}\Big|=\frac{|x'|}{v_st'}\,\beta^2t',$$
--
--   so $|\beta\cdot r'/c|\ll\beta^2t'$ exactly when $|x'|\ll v_st'$, which holds for $|x'|\simeq10$-$100$ m at all but very small $t'$. Moreover $\beta\cdot r'=0$ if and only if $x'=0$, i.e. the shift vanishes exactly for antennae on a line perpendicular to the satellite's displacement.
--
--   **Formalization Note** The paper's informal "$|\beta\cdot r'/c|\ll\beta^2t'$ for almost all $t'$" is stated as the exact ratio $|\beta\cdot r'/c|/(\beta^2t')=|x'|/(v_st')$, from which it follows under the paper's condition $|x'|\ll v_st'$.
-- source:
--   Braun, Monjid, Rougé and Kerr, Generalization of the Van Cittert-Zernike theorem: observers moving with respect to sources, arXiv:1506.04764v1 (2015), claim c005; Sec. 2.2, paragraph after eq. (13), PDF p. 6

import Mathlib
import Definitions.Def_Arxiv1506_04764_Basic

open MeasureTheory Complex

namespace Arxiv1506_04764

theorem time_shift_beta_r_negligible (c vs x y h t' : ℝ)
    (hc : 0 < c) (hvs : 0 < vs) (hvc : vs < c) (ht' : 0 < t') :
    |dotProduct (betaVec c ![vs, 0, 0]) ![x, y, h] / c| =
        |x| / (vs * t') * ((vs / c) ^ 2 * t') ∧
      (dotProduct (betaVec c ![vs, 0, 0]) ![x, y, h] = 0 ↔ x = 0) := by sorry

end Arxiv1506_04764
