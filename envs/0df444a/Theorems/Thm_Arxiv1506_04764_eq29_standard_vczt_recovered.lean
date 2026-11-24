-- Prove2me | Theorems.Thm_Arxiv1506_04764_eq29_standard_vczt_recovered
-- name    : Arxiv1506_04764.eq29_standard_vczt_recovered
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T15:36:08.705923+00:00
-- url     : https://prove2.me/theorems/dd78fee4-0bb3-4c0e-9ce2-9c390ea85d14
-- title:
--   Eq. (29): the standard Van Cittert-Zernike form at equal times and small bandwidth
-- statement:
--   There are constants $M$ and $\delta>0$ such that for all $l_c,T_c,\mu_0,\omega_0,b,c>0$, every source strength $S\ge0$ with $S(r'')/(|r_1'-r''||r_2'-r''|)$ integrable, and all antenna positions with $b|\Delta r|/c\le\delta$, the correlation function (28) at equal times ($\Delta t=0$) differs from the standard Van Cittert-Zernike form
--
--   $$C_{VCZ}=K\int d^3r''\,S(r'')\,\frac{\exp\big[i\omega_0\frac1c\Delta r\cdot\hat e_{r_1'-r''}\big]}{|r_1'-r''||r_2'-r''|}$$
--
--   by at most
--
--   $$M\Big(\frac{b|\Delta r|}{c}\Big)^2K\int d^3r''\,\frac{S(r'')}{|r_1'-r''||r_2'-r''|}.$$
--
--   Thus (28) reduces to (29) for $\Delta t=0$ and $b|\Delta r|/c\ll1$. Neither expression contains $v_s$.
--
--   **Formalization Note** The paper's "$\operatorname{sinc}\simeq1$ for $b\Delta r/c\ll1$" is stated as an explicit relative error bound of order $(b|\Delta r|/c)^2$ for $b|\Delta r|/c$ at most some $\delta>0$; $|\Delta r|$ is the length of the baseline. The paper's further conclusion that (29) is valid at finite observer speed to first order in $\beta$ rests on (27), whose derivation omits a first-order phase term (see the statement on eqs. (25)-(27)); it is not part of this statement.
-- source:
--   Braun, Monjid, Rougé and Kerr, Generalization of the Van Cittert-Zernike theorem: observers moving with respect to sources, arXiv:1506.04764v1 (2015), claim c011; Sec. 3, eq. (29) and the following paragraph, PDF p. 10

import Mathlib
import Definitions.Def_Arxiv1506_04764_Basic

open MeasureTheory Complex

namespace Arxiv1506_04764

theorem eq29_standard_vczt_recovered :
    ∃ M δ : ℝ, 0 < δ ∧ ∀ (lc Tc mu0 omega0 b c : ℝ) (S : V3 → ℝ) (r1 r2 : V3),
      0 < lc → 0 < Tc → 0 < mu0 → 0 < omega0 → 0 < b → 0 < c → (∀ r, 0 ≤ S r) →
      Integrable (fun r'' => S r'' / (len (r1 - r'') * len (r2 - r''))) →
      b * len (r2 - r1) / c ≤ δ →
      ‖corrEq28 (constK lc b omega0 mu0 Tc) omega0 b c S r1 r2 0 -
          corrVCZ (constK lc b omega0 mu0 Tc) omega0 c S r1 r2‖ ≤
        M * (b * len (r2 - r1) / c) ^ 2 *
          (constK lc b omega0 mu0 Tc * ∫ r'', S r'' / (len (r1 - r'') * len (r2 - r''))) := by sorry

end Arxiv1506_04764
