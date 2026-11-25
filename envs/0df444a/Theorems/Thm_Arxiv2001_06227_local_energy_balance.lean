-- Prove2me | Theorems.Thm_Arxiv2001_06227_local_energy_balance
-- name    : Arxiv2001_06227.local_energy_balance
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T07:49:14.179888+00:00
-- url     : https://prove2.me/theorems/dd063d1a-5992-59b2-9912-398d5d56bff8
-- title:
--   Eq. (54): local energy balance $P_e=P_a+P_s$
-- statement:
--   Let $\epsilon_0,\mu_0,c,\omega>0$ with $\mu_0\epsilon_0c^2=1$ and $k_0=\omega/c$. Let $\delta\epsilon,E_0,E_s:\mathbb{R}^3\to\mathbb{C}$, with $E_s$ of class $C^2$, satisfy
--
--   $$\Delta E_s+k_0^2E_s=-k_0^2\,\delta\epsilon\,E,\qquad E=E_0+E_s.$$
--
--   With $j=-i\omega\epsilon_0\,\delta\epsilon\,E$ and $J_s=\frac1{2\mu_0\omega}\operatorname{Im}(E_s^*\nabla E_s)$, at every point $r$
--
--   $$\tfrac12\operatorname{Re}[j(r)E_0^*(r)]=\tfrac12\operatorname{Re}[j(r)E^*(r)]+\nabla\cdot J_s(r),$$
--
--   that is, $\mathcal{P}_e=\mathcal{P}_a+\mathcal{P}_s$.
--
--   **Formalization Note** $J_s$ is taken with the sign of Appendix B; with the sign printed in eq. (53) the identity would read $\mathcal{P}_e=\mathcal{P}_a-\mathcal{P}_s$. Twice continuous differentiability of $E_s$ is the regularity under which the Laplacian in eq. (6) is taken pointwise.
-- source:
--   Sheremet, Pierrat and Carminati, Absorption of scalar waves in correlated disordered media and its maximization using stealth hyperuniformity, arXiv:2001.06227v2 (2020), claim c005; Section IV.A, eq. (54), with eqs. (51)-(53); proof in Appendix B, eqs. (B1)-(B5), PDF pp. 6 and 10

import Mathlib
import Definitions.Def_Arxiv2001_06227_Basic

open MeasureTheory Filter Topology

namespace Arxiv2001_06227

theorem local_energy_balance (eps0 mu0 c omega : ℝ) (heps0 : 0 < eps0) (hmu0 : 0 < mu0)
    (hc : 0 < c) (homega : 0 < omega) (hvac : mu0 * eps0 * c ^ 2 = 1)
    (deps E0 Es : Space → ℂ) (hEs : ContDiff ℝ 2 Es)
    (hsca : IsScatteredField c omega deps E0 Es) (x : Space) :
    extPower (inducedCurrent eps0 omega deps (E0 + Es)) E0 x =
      absPower (inducedCurrent eps0 omega deps (E0 + Es)) (E0 + Es) x + scaPower mu0 omega Es x := by sorry

end Arxiv2001_06227
