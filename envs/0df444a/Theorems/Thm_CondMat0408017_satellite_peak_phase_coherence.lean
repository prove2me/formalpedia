-- Prove2me | Theorems.Thm_CondMat0408017_satellite_peak_phase_coherence
-- name    : CondMat0408017.satellite_peak_phase_coherence
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:23:54.690882+00:00
-- url     : https://prove2.me/theorems/6262f62c-4dd7-42a5-80d9-e78c6be2e01e
-- title:
--   Eqs. (135)-(136): phase difference of reciprocal double-scattering paths and the angles of the backscattering and satellite peaks
-- statement:
--   Let the incident medium have dielectric constant $\varepsilon_0>0$, let $\omega,c>0$, and let $q_n,q_m$ be the wave numbers of two guided (or surface) modes. Let $k_0=\sqrt{\varepsilon_0}\frac\omega c(\sin\theta_0,-\cos\theta_0)$ and $k_s=\sqrt{\varepsilon_0}\frac\omega c(\sin\theta_s,\cos\theta_s)$. Let $\Delta\phi_{nm}$ be the phase of the path that enters at $C$, travels to $B$ in mode $n$ and leaves along $k_s$, minus the phase of the path that enters at $B$, travels to $C$ in mode $m$ and leaves along $k_s$. Then:
--
--   1. (eq. 135) For all points $B,C$ in the $(x_1,x_3)$ plane, $\Delta\phi_{nm}=r_{BC}\cdot(k_0+k_s)+|r_{BC}|(q_n-q_m)$ with $r_{BC}=r_C-r_B$.
--   2. For scattering centres on the mean surface with $x_B<x_C$, $\Delta\phi_{nm}=0$ if and only if $\sin\theta_s=-\sin\theta_0-\frac{1}{\sqrt{\varepsilon_0}}\frac c\omega(q_n-q_m)$. This condition does not depend on the distance $x_C-x_B$.
--   3. (eq. 136) Some pair of distinct centres on the mean surface gives $\Delta\phi_{nm}=0$ if and only if
--   $$\sin\theta_s=-\sin\theta_0\pm\frac{1}{\sqrt{\varepsilon_0}}\frac{c}{\omega}|q_n(\omega)-q_m(\omega)|$$
--   for one of the two signs.
--
--   For $m=n$ this is the backscattering direction $\theta_s=-\theta_0$, and for $m\ne n$ it gives the satellite peaks.
--
--   **Formalization Note** The phase of a path is $k_0\cdot r_{\rm in}+q|r_{\rm out}-r_{\rm in}|-k_s\cdot r_{\rm out}$, so (135) is derived rather than assumed. The sign $\pm$ in (136) corresponds to the orientation of $r_{BC}$ along the surface. Requiring $\Delta\phi_{nm}=0$ for $r_{BC}$ of both orientations at once would force $q_n=q_m$ (see the report). Higher-order paths, which the paper says do not change the conclusion, are not treated.
-- source:
--   I. Simonsen, A random walk through surface scattering phenomena: Theory and phenomenology, arXiv:cond-mat/0408017v1 (2004), claim c040; Sec. IV.A.3, eqs. (Eq:Phen:Phase-diff), (Eq:Phen:Angels) [(135)-(136)], PDF p. 46

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex

namespace CondMat0408017

theorem satellite_peak_phase_coherence (eps0 ω c θ0 θs qn qm : ℝ) (heps0 : 0 < eps0)
    (hω : 0 < ω) (hc : 0 < c) :
    (∀ rB rC : ℝ × ℝ, doublePathPhaseDiff eps0 ω c θ0 θs qn qm rB rC =
      dot2 (rC - rB) (incWaveVec eps0 ω c θ0 + scatWaveVec eps0 ω c θs) +
        eucl (rC - rB) * (qn - qm)) ∧
    (∀ xB xC : ℝ, xB < xC →
      (doublePathPhaseDiff eps0 ω c θ0 θs qn qm (xB, 0) (xC, 0) = 0 ↔
        Real.sin θs = -Real.sin θ0 - 1 / Real.sqrt eps0 * (c / ω) * (qn - qm))) ∧
    ((∃ xB xC : ℝ, xB ≠ xC ∧ doublePathPhaseDiff eps0 ω c θ0 θs qn qm (xB, 0) (xC, 0) = 0) ↔
      (Real.sin θs = -Real.sin θ0 + 1 / Real.sqrt eps0 * (c / ω) * |qn - qm| ∨
        Real.sin θs = -Real.sin θ0 - 1 / Real.sqrt eps0 * (c / ω) * |qn - qm|)) := by sorry

end CondMat0408017
