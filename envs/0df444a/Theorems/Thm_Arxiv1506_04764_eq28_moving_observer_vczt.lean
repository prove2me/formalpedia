-- Prove2me | Theorems.Thm_Arxiv1506_04764_eq28_moving_observer_vczt
-- name    : Arxiv1506_04764.eq28_moving_observer_vczt
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T15:23:56.284485+00:00
-- url     : https://prove2.me/theorems/02e6acae-e9e7-454f-9f93-829d1bc9dcdb
-- title:
--   Eq. (28): Van Cittert-Zernike theorem for a moving observer and a finite time interval
-- statement:
--   Let $l_c,T_c,\mu_0,\omega_0,b,c>0$, let $S\ge0$ be the source strength with $r''\mapsto S(r'')/(|r_1'-r''||r_2'-r''|)$ integrable on $\mathbb R^3$, and let $w$ be the rectangular filter of bandwidth $b$, $w(\omega)=1$ for $\omega_0-b/2\le\omega\le\omega_0+b/2$ and $0$ elsewhere. Then the right-hand side of eq. (27) equals
--
--   $$C(r_1',t_1',r_2',t_2')=K\int d^3r''\,S(r'')\,\frac{\exp\big[i\omega_0\big(-\Delta t+\frac1c\Delta r\cdot\hat e_{r_1'-r''}\big)\big]}{|r_1'-r''||r_2'-r''|}\,\operatorname{sinc}\Big[\frac b2\Big(-\Delta t+\frac1c\Delta r\cdot\hat e_{r_1'-r''}\Big)\Big],$$
--
--   where $\operatorname{sinc}(x)=\sin(x)/x$ and $K=l_c^3b\,\omega_0^2\mu_0^2/(32\pi^3T_c)$.
--
--   **Formalization Note** The paper derives (28) from (27) by carrying out the frequency integral; that step is exact and is what is stated, with the paper's order of integration ($\omega$ outside). The approximations by which the paper reaches (27) are not part of this statement (see the statement on eqs. (25)-(27)). The integrability of the source term, implicit in the paper, is a hypothesis; $\operatorname{sinc}(0)=1$.
-- source:
--   Braun, Monjid, Rougé and Kerr, Generalization of the Van Cittert-Zernike theorem: observers moving with respect to sources, arXiv:1506.04764v1 (2015), claim c015; Sec. 2.4, eqs. (27)-(28), PDF p. 9 (filter band values Sec. 2.3, PDF p. 7)

import Mathlib
import Definitions.Def_Arxiv1506_04764_Basic

open MeasureTheory Complex

namespace Arxiv1506_04764

theorem eq28_moving_observer_vczt (lc Tc mu0 omega0 b c : ℝ) (S : V3 → ℝ) (r1 r2 : V3) (dt : ℝ)
    (hlc : 0 < lc) (hTc : 0 < Tc) (hmu0 : 0 < mu0) (homega0 : 0 < omega0) (hb : 0 < b)
    (hc : 0 < c) (hS : ∀ r, 0 ≤ S r)
    (hint : Integrable (fun r'' => S r'' / (len (r1 - r'') * len (r2 - r'')))) :
    corrEq27 lc Tc mu0 omega0 c S (rectFilter omega0 b) r1 r2 dt =
      corrEq28 (constK lc b omega0 mu0 Tc) omega0 b c S r1 r2 dt := by sorry

end Arxiv1506_04764
