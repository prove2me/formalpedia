-- Prove2me | Theorems.Thm_Arxiv1506_04764_eq26_doppler_cancellation_exact
-- name    : Arxiv1506_04764.eq26_doppler_cancellation_exact
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T15:08:30.66667+00:00
-- url     : https://prove2.me/theorems/3e899968-a826-4740-aa8d-9a66be11cfa9
-- title:
--   Eqs. (25)-(27): Doppler and virtual-baseline phases cancel (as proved, exact form of the frequency substitution)
-- statement:
--   Let $l_c,T_c,\mu_0,\omega_0,c>0$, let $v_s$ be the satellite velocity with $|v_s|<c$ and $\beta=v_s/c$, let $S\ge0$ be the source strength, $w$ any filter, $r_1',r_2'$ the antenna positions, $\Delta r=r_2'-r_1'$, $\Delta t$ the time interval, and for each source point write $\hat e=\hat e_{r_1'-r''}$ and $\kappa=1-\hat e\cdot\beta>0$. Then the right-hand side of eq. (25) with the flat-spectrum replacement $\omega^2\langle|\tilde J(r'',\omega)|^2\rangle\to\omega_0^2S(r'')$ equals exactly
--
--   $$\frac{l_c^3}{2\pi T_c}\Big(\frac{\mu_0}{4\pi}\Big)^2\int d^3r''\,\frac{\omega_0^2S(r'')}{\kappa\,|r_1'-r''||r_2'-r''|}\int d\omega\,|w(\omega)|^2\exp\Big[i\omega\Big(-\Delta t+\frac{\Delta r\cdot\hat e}{c\,\kappa}\Big)\Big].$$
--
--   In particular the Doppler phase and the virtual-baseline phase $(\omega/c)\Delta t\,v_s\cdot\hat e$ cancel exactly in the $\Delta t$-term: the velocity enters only through the amplitude factor $1/\kappa$ and the factor $1/\kappa$ multiplying $\Delta r\cdot\hat e/c$. Dropping these two factors (corrections of order $\beta$ in the amplitude and of order $\beta\,|\Delta r|\omega/c$ in the phase) gives eq. (27).
--
--   **Formalization Note** This is what the step (25)$\to$(26)$\to$(27) establishes when the inverse substitution $\omega\to\omega/(1-\hat e\cdot\beta)$ is applied to the whole integrand. The paper applies it, to first order, only to the term $-i\omega\Delta t$, which yields (26) without the phase $i(\omega/c)(\hat e\cdot\beta)(\Delta r\cdot\hat e)$; that term is first order in $\beta$ and does not cancel. (27) is therefore not an identity and is not stated; the exact identity is stated instead (as proved). The source integral is written outside the frequency integral (the substitution depends on $r''$; the paper's order of integration requires an interchange).
-- source:
--   Braun, Monjid, Rougé and Kerr, Generalization of the Van Cittert-Zernike theorem: observers moving with respect to sources, arXiv:1506.04764v1 (2015), claim c014; Sec. 2.4, eqs. (25)-(27) and the following sentence, PDF pp. 8-9

import Mathlib
import Definitions.Def_Arxiv1506_04764_Basic

open MeasureTheory Complex

namespace Arxiv1506_04764

theorem eq26_doppler_cancellation_exact (lc Tc mu0 omega0 c : ℝ) (S : V3 → ℝ) (w : ℝ → ℂ)
    (vs r1 r2 : V3) (dt : ℝ)
    (hlc : 0 < lc) (hTc : 0 < Tc) (hmu0 : 0 < mu0) (homega0 : 0 < omega0) (hc : 0 < c)
    (hvs : len vs < c) (hS : ∀ r, 0 ≤ S r) :
    corrEq25Flat lc Tc mu0 omega0 c S w vs r1 r2 dt =
      ((lc ^ 3 / (2 * Real.pi * Tc) * (mu0 / (4 * Real.pi)) ^ 2 : ℝ) : ℂ) *
        ∫ r'', ((omega0 ^ 2 * S r'' / (len (r1 - r'') * len (r2 - r'')) /
            (1 - dotProduct (unitVec (r1 - r'')) (betaVec c vs)) : ℝ) : ℂ) *
          ∫ omega : ℝ, ((‖w omega‖ ^ 2 : ℝ) : ℂ) *
            Complex.exp (I * omega *
              ((-dt + dotProduct (r2 - r1) (unitVec (r1 - r'')) /
                (c * (1 - dotProduct (unitVec (r1 - r'')) (betaVec c vs))) : ℝ) : ℂ)) := by sorry

end Arxiv1506_04764
