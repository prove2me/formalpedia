-- Prove2me | Theorems.Thm_CondMat0408017_intensity_correlation_decomposition
-- name    : CondMat0408017.intensity_correlation_decomposition
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-26T13:25:12.940096+00:00
-- url     : https://prove2.me/theorems/bb2f69b2-909f-4cd2-93fe-a63343014a90
-- title:
--   Sec. IV.C.1: the off-specular intensity correlation function splits into $C^{(1)}+C^{(10)}+C^{(N)}$
-- statement:
--   Let $S_1=S(q|k)$ and $S_2=S(q'|k')$ be complex random variables with finite fourth moments at off-specular arguments, where stationarity gives $\langle S(q|k)\rangle=2\pi\delta(q-k)S(k)=0$, so $\langle S_1\rangle=\langle S_2\rangle=0$. Let $\delta S=S-\langle S\rangle$. Then the angular intensity correlation function
--
--   $$C=\frac{\varepsilon_0}{L_1^2}\frac{\omega^2}{c^2}\big[\langle|S_1|^2|S_2|^2\rangle-\langle|S_1|^2\rangle\langle|S_2|^2\rangle\big]$$
--
--   splits exactly as $C=C^{(1)}+C^{(10)}+C^{(N)}$ with
--
--   $$C^{(1)}=\frac{\varepsilon_0}{L_1^2}\frac{\omega^2}{c^2}|\langle\delta S_1\,\delta S_2^*\rangle|^2,\qquad C^{(10)}=\frac{\varepsilon_0}{L_1^2}\frac{\omega^2}{c^2}|\langle\delta S_1\,\delta S_2\rangle|^2,\qquad C^{(N)}=\frac{\varepsilon_0}{L_1^2}\frac{\omega^2}{c^2}\{\delta S_1\,\delta S_1^*\,\delta S_2\,\delta S_2^*\},$$
--
--   where $\{\cdot\}$ is the fourth-order joint cumulant.
--
--   **Formalization Note** The paper writes $C=C^{(1)}+C^{(10)}+C^{(N)}+\text{s.t.}$, with specular terms proportional to $\delta(q-k)$ or $\delta(q'-k')$ that it drops. Away from the specular directions, $q\ne k$ and $q'\ne k'$, these terms are absent. This is encoded by the hypotheses $\langle S_1\rangle=\langle S_2\rangle=0$, the off-specular content of (Eq:Phen:avr-S-matrix). The cumulant of four variables is the standard joint cumulant; the paper defines only the two-variable case $\{AB\}=\langle AB\rangle-\langle A\rangle\langle B\rangle$ and cites [Corr21] for the rest.
-- source:
--   I. Simonsen, A random walk through surface scattering phenomena: Theory and phenomenology, arXiv:cond-mat/0408017v1 (2004), claim c046; Sec. IV.C.1, eqs. (Eq:Phen:Rewritten), (Eq:Phen:avr-S-matrix), (Eq:Phen:C-Rewritten), (PHEN:Eq:Rewritten), (PHEN:Eq:C1), (PHEN:Eq:C10), (PHEN:Eq:CN), PDF pp. 53-54

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex

namespace CondMat0408017

theorem intensity_correlation_decomposition {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (eps0 L1 wv : ℝ) (S1 S2 : Ω → ℂ) (h1 : MemLp S1 4 P)
    (h2 : MemLp S2 4 P) (hm1 : ∫ w, S1 w ∂P = 0) (hm2 : ∫ w, S2 w ∂P = 0) :
    (intensityCorrelation P eps0 L1 wv S1 S2 : ℂ) =
      ((eps0 / L1 ^ 2 * wv ^ 2 *
          ‖∫ w, fluct P S1 w * starRingEnd ℂ (fluct P S2 w) ∂P‖ ^ 2 : ℝ) : ℂ) +
        ((eps0 / L1 ^ 2 * wv ^ 2 * ‖∫ w, fluct P S1 w * fluct P S2 w ∂P‖ ^ 2 : ℝ) : ℂ) +
        ((eps0 / L1 ^ 2 * wv ^ 2 : ℝ) : ℂ) *
          cumulant4 P (fluct P S1) (fun w => starRingEnd ℂ (fluct P S1 w)) (fluct P S2)
            (fun w => starRingEnd ℂ (fluct P S2 w)) := by sorry

end CondMat0408017
