-- Prove2me | Theorems.Thm_Arxiv2001_06227_average_power_splitting
-- name    : Arxiv2001_06227.average_power_splitting
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T07:59:14.721124+00:00
-- url     : https://prove2.me/theorems/54099181-9444-4cae-94a5-3f6f4f4f59a5
-- title:
--   Eqs. (56)-(60): splitting of the average absorbed power, $\langle P_a\rangle=\overline{P}_a-\widetilde{P}_s$
-- statement:
--   Let $\epsilon_0,\mu_0,c,\omega>0$ with $\mu_0\epsilon_0c^2=1$, $k_0=\omega/c$, and let realizations of disorder be the points $\xi$ of a probability space $(\Omega,P)$. Let the incident field $E_0$ be deterministic and, for every $\xi$, let $\delta\epsilon_\xi$ and the $C^2$ scattered field $E_{s,\xi}$ satisfy eq. (6), $\Delta E_{s,\xi}+k_0^2E_{s,\xi}=-k_0^2\delta\epsilon_\xi E_\xi$ with $E_\xi=E_0+E_{s,\xi}$. Assume $\delta\epsilon_\xi(r)$ and $E_{s,\xi}(r)$ are measurable in $\xi$ for each $r$, and $|\delta\epsilon|$, $|E_s|$ and the first and second derivatives of $E_s$ are bounded by one constant for all $\xi,r$. Assume (absence of non-locality) that the average scattered field obeys a Helmholtz equation with an effective dielectric function: $\Delta\langle E_s\rangle+k_0^2\langle E_s\rangle=-k_0^2\epsilon_{\rm eff}\langle E\rangle$ for some $\epsilon_{\rm eff}:\mathbb{R}^3\to\mathbb{C}$. Then at every point $r$:
--
--   1. $\langle\mathcal{P}_e\rangle=\overline{\mathcal{P}}_e$;
--   2. $\langle\mathcal{P}_a\rangle=\overline{\mathcal{P}}_a+\widetilde{\mathcal{P}}_a$ and $\langle\mathcal{P}_s\rangle=\overline{\mathcal{P}}_s+\widetilde{\mathcal{P}}_s$ (eq. 56);
--   3. $\overline{\mathcal{P}}_e=\overline{\mathcal{P}}_a+\widetilde{\mathcal{P}}_a+\overline{\mathcal{P}}_s+\widetilde{\mathcal{P}}_s$ (eq. 57);
--   4. $\overline{\mathcal{P}}_e=\overline{\mathcal{P}}_a+\overline{\mathcal{P}}_s$ (eq. 58);
--   5. $\widetilde{\mathcal{P}}_a+\widetilde{\mathcal{P}}_s=0$ (eq. 59);
--   6. $\langle\mathcal{P}_a\rangle=\overline{\mathcal{P}}_a-\widetilde{\mathcal{P}}_s$ (eq. 60).
--
--   Here $\overline{\mathcal{P}}_e=\tfrac12\operatorname{Re}[\langle j\rangle E_0^*]$, $\overline{\mathcal{P}}_a=\tfrac12\operatorname{Re}[\langle j\rangle\langle E\rangle^*]$, $\overline{\mathcal{P}}_s=\nabla\cdot J_s[\langle E_s\rangle]$, $\widetilde{\mathcal{P}}_a=\langle\tfrac12\operatorname{Re}[\delta j\,\delta E^*]\rangle$, $\widetilde{\mathcal{P}}_s=\langle\nabla\cdot J_s[\delta E_s]\rangle$.
--
--   **Formalization Note** The paper does not state regularity or integrability conditions; measurability in $\xi$, $C^2$ realizations and a uniform bound on $\delta\epsilon$, $E_s$ and its first two derivatives are added so that averages exist and commute with derivatives. The splitting (56) is made explicit by the definitions of the barred and tilded terms listed above. The effective-medium hypothesis is the paper's; eq. (58) also follows without it, by averaging eq. (6).
-- source:
--   Sheremet, Pierrat and Carminati, Absorption of scalar waves in correlated disordered media and its maximization using stealth hyperuniformity, arXiv:2001.06227v2 (2020), claim c006; Section IV.A, eqs. (55)-(60), PDF p. 6

import Mathlib
import Definitions.Def_Arxiv2001_06227_Basic

open MeasureTheory Filter Topology

namespace Arxiv2001_06227

theorem average_power_splitting {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (eps0 mu0 c omega : ℝ) (heps0 : 0 < eps0) (hmu0 : 0 < mu0)
    (hc : 0 < c) (homega : 0 < omega) (hvac : mu0 * eps0 * c ^ 2 = 1)
    (deps : Ω → Space → ℂ) (E0 : Space → ℂ) (Es : Ω → Space → ℂ)
    (hmeas : ∀ x, AEStronglyMeasurable (fun ξ => deps ξ x) P ∧
      AEStronglyMeasurable (fun ξ => Es ξ x) P)
    (hsmooth : ∀ ξ, ContDiff ℝ 2 (Es ξ))
    (hbound : ∃ C : ℝ, ∀ ξ x, ‖deps ξ x‖ ≤ C ∧ ‖Es ξ x‖ ≤ C ∧ ‖fderiv ℝ (Es ξ) x‖ ≤ C ∧
      ‖fderiv ℝ (fderiv ℝ (Es ξ)) x‖ ≤ C)
    (hsca : ∀ ξ, IsScatteredField c omega (deps ξ) E0 (Es ξ))
    (heff : ∃ epsEff : Space → ℂ, IsScatteredField c omega epsEff E0 (ensAvg P Es)) (x : Space) :
    meanExtPower P eps0 omega deps E0 Es x = barExtPower P eps0 omega deps E0 Es x ∧
    meanAbsPower P eps0 omega deps E0 Es x =
      barAbsPower P eps0 omega deps E0 Es x + tildeAbsPower P eps0 omega deps E0 Es x ∧
    meanScaPower P mu0 omega Es x = barScaPower P mu0 omega Es x + tildeScaPower P mu0 omega Es x ∧
    barExtPower P eps0 omega deps E0 Es x =
      barAbsPower P eps0 omega deps E0 Es x + tildeAbsPower P eps0 omega deps E0 Es x +
        barScaPower P mu0 omega Es x + tildeScaPower P mu0 omega Es x ∧
    barExtPower P eps0 omega deps E0 Es x =
      barAbsPower P eps0 omega deps E0 Es x + barScaPower P mu0 omega Es x ∧
    tildeAbsPower P eps0 omega deps E0 Es x + tildeScaPower P mu0 omega Es x = 0 ∧
    meanAbsPower P eps0 omega deps E0 Es x =
      barAbsPower P eps0 omega deps E0 Es x - tildeScaPower P mu0 omega Es x := by sorry

end Arxiv2001_06227
