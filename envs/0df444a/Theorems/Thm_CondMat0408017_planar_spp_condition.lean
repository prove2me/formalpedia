-- Prove2me | Theorems.Thm_CondMat0408017_planar_spp_condition
-- name    : CondMat0408017.planar_spp_condition
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:18:51.555574+00:00
-- url     : https://prove2.me/theorems/8b5a172b-3488-505d-957a-37baef419dca
-- title:
--   Eqs. (17)-(19): existence condition and dispersion relation of surface plasmon polaritons at a planar interface
-- statement:
--   Let a planar interface $x_3=0$ separate media of real dielectric constants $\varepsilon_+$ ($x_3>0$) and $\varepsilon_-$ ($x_3<0$). Let $c,\omega>0$, and let $k$ be such that $k^2-\varepsilon_\pm\omega^2/c^2>0$, so that $\beta_\pm=\sqrt{k^2-\varepsilon_\pm\omega^2/c^2}>0$. Consider $\Phi^+=A^+e^{-\beta_+x_3}e^{ikx_1}$ and $\Phi^-=A^-e^{\beta_-x_3}e^{ikx_1}$.
--
--   1. For any non-zero $\kappa^\pm$, the boundary conditions $\Phi^+=\Phi^-$, $\frac1{\kappa^+}\partial_3\Phi^+=\frac1{\kappa^-}\partial_3\Phi^-$ at $x_3=0$ hold if and only if $A^+=A^-\equiv A$ and (eq. 17)
--   $$\Big(\frac{\beta_+}{\kappa^+}+\frac{\beta_-}{\kappa^-}\Big)A=0 .$$
--   2. ($s$ polarization, non-magnetic media) If $\kappa^\pm=\mu_0>0$, the only solution is $A^+=A^-=0$: there is no $s$-polarized SPP.
--   3. ($p$ polarization) Let $\varepsilon_\pm\ne0$ and $\kappa^\pm=\varepsilon_\pm$. A solution with $(A^+,A^-)\ne0$ exists if and only if (eq. 18)
--   $$\frac{\varepsilon_+}{\varepsilon_-}=-\frac{\beta_+}{\beta_-} .$$
--   This holds if and only if $\varepsilon_+\varepsilon_-<0$, $\varepsilon_++\varepsilon_-\ne0$ and (eq. 19)
--   $$k=\pm\sqrt{\frac{\varepsilon_+\varepsilon_-}{\varepsilon_++\varepsilon_-}}\,\frac\omega c .$$
--
--   **Formalization Note** The last equivalence includes the paper's remark that (19), obtained by squaring, holds only together with $\beta_\pm>0$ and opposite signs of $\varepsilon_\pm$. These are sufficient, as the paper says. The paper's footnote, that the conclusion is unchanged for complex $\varepsilon_\pm$ with $\operatorname{Re}\beta_\pm>0$, is asserted without derivation and is not part of the statement.
-- source:
--   I. Simonsen, A random walk through surface scattering phenomena: Theory and phenomenology, arXiv:cond-mat/0408017v1 (2004), claim c001; Sec. II.D.1, eqs. (Elmag:SPP-condition), (Elmag:SPP-dipersion-relation-1), (Elmag:dispersion-relation) [(17)-(19)], PDF p. 10

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex

namespace CondMat0408017

theorem planar_spp_condition (epsP epsM k ω c : ℝ) (hc : 0 < c) (hω : 0 < ω)
    (hP : 0 < k ^ 2 - epsP * (ω / c) ^ 2) (hM : 0 < k ^ 2 - epsM * (ω / c) ^ 2) :
    (∀ κP κM AP AM : ℂ, κP ≠ 0 → κM ≠ 0 →
      (FlatInterfaceBC κP κM (planarModeUpper AP (decayConst epsP k ω c) k)
          (planarModeLower AM (decayConst epsM k ω c) k) ↔
        AP = AM ∧
          ((decayConst epsP k ω c : ℂ) / κP + (decayConst epsM k ω c : ℂ) / κM) * AP = 0)) ∧
    (∀ (μ0 : ℝ) (AP AM : ℂ), 0 < μ0 →
      FlatInterfaceBC (μ0 : ℂ) (μ0 : ℂ) (planarModeUpper AP (decayConst epsP k ω c) k)
          (planarModeLower AM (decayConst epsM k ω c) k) → AP = 0 ∧ AM = 0) ∧
    (epsP ≠ 0 → epsM ≠ 0 →
      ((∃ AP AM : ℂ, (AP ≠ 0 ∨ AM ≠ 0) ∧
          FlatInterfaceBC (epsP : ℂ) (epsM : ℂ) (planarModeUpper AP (decayConst epsP k ω c) k)
            (planarModeLower AM (decayConst epsM k ω c) k)) ↔
        epsP / epsM = -(decayConst epsP k ω c / decayConst epsM k ω c)) ∧
      (epsP / epsM = -(decayConst epsP k ω c / decayConst epsM k ω c) ↔
        epsP * epsM < 0 ∧ epsP + epsM ≠ 0 ∧
          (k = Real.sqrt (epsP * epsM / (epsP + epsM)) * (ω / c) ∨
            k = -(Real.sqrt (epsP * epsM / (epsP + epsM)) * (ω / c))))) := by sorry

end CondMat0408017
