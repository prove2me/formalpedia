-- Prove2me | Theorems.Thm_Arxiv1801_00461_model_case_x_pm_half
-- name    : Arxiv1801_00461.model_case_x_pm_half
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:16:36.865265+00:00
-- url     : https://prove2.me/theorems/50d445ec-5906-41d6-b62f-3b9d71e59d01
-- title:
--   Eqs. (44)-(46) (as proved): the cases $x=\pm 1/2$ of the model (38)
-- statement:
--   Let $\varepsilon_o>0$, $\kappa>0$, and $\varepsilon_A=\varepsilon_o+\kappa/|\omega|^{2+x}$ with $x=\pm1/2$. Then the principal values of eq. (42) exist and $\kappa_1=\mp\kappa$, the upper sign for $x=+1/2$ (eq. (45)). For every $\omega>0$:
--
--   1. $\mathcal H(\bar\Delta(\omega\varepsilon_A))(\omega)=-\kappa/\omega^{3/2}$ for $x=1/2$ and $=\kappa/\omega^{1/2}$ for $x=-1/2$;
--   2. $\tan\phi=\bar\Delta(\omega\varepsilon_A)/\bar\Delta\sigma_A=+1$ for $x=1/2$ and $-1$ for $x=-1/2$ (eq. (46));
--   3. the admittance variation is $\bar\Delta\gamma_A=\bar\Delta\sigma_A\,(1+i)$ for $\varepsilon_A=\varepsilon_o+\kappa/|\omega|^{5/2}$ and $\bar\Delta\gamma_A=\bar\Delta\sigma_A\,(1-i)$ for $\varepsilon_A=\varepsilon_o+\kappa/|\omega|^{3/2}$;
--   4. its argument is $\pi/4$ for $x=1/2$ and $3\pi/4$ for $x=-1/2$.
--
--   **Formalization Note** Here $\bar\Delta\gamma_A=\bar\Delta\sigma_A+i\bar\Delta(\omega\varepsilon_A)$ with $\bar\Delta\sigma_A=-\mathcal H(\bar\Delta(\omega\varepsilon_A))$. The paper writes $\phi=\pm\pi/4$. For $x=-1/2$ one has $\bar\Delta\sigma_A=-\kappa/\sqrt\omega<0$, so the argument is $3\pi/4$, which has the printed tangent $-1$. The printed argument of the logarithm in eq. (45) contains factors that appear to be typographical errors. The statement records the values, not the printed intermediate expression.
-- source:
--   Bédard and Destexhe, Kramers-Kronig relations and the properties of conductivity and permittivity in heterogeneous media, arXiv:1801.00461v1 (2018), claim c019; Sec. 3.1.2, Case x = ±1/2, eqs. (44)-(46) and the following sentence, PDF p. 14

import Mathlib
import Definitions.Def_Arxiv1801_00461_Basic

open MeasureTheory Filter Topology

namespace Arxiv1801_00461

theorem model_case_x_pm_half (eps0 kappa : ℝ) (heps0 : 0 < eps0) (hkappa : 0 < kappa) :
    (∃ P : ℝ, Tendsto (kernelTrunc (1 / 2)) (𝓝[>] 0) (𝓝 P)) ∧
    (∃ P : ℝ, Tendsto (kernelTrunc (-1 / 2)) (𝓝[>] 0) (𝓝 P)) ∧
    kappaOne kappa (1 / 2) = -kappa ∧ kappaOne kappa (-1 / 2) = kappa ∧
    ∀ ω : ℝ, 0 < ω →
      HasHilbert (omegaEpsDev eps0 kappa (1 / 2)) ω (-kappa / ω ^ (3 / 2 : ℝ)) ∧
      HasHilbert (omegaEpsDev eps0 kappa (-1 / 2)) ω (kappa / ω ^ (1 / 2 : ℝ)) ∧
      omegaEpsDev eps0 kappa (1 / 2) ω / appCondDevModel eps0 kappa (1 / 2) ω = 1 ∧
      omegaEpsDev eps0 kappa (-1 / 2) ω / appCondDevModel eps0 kappa (-1 / 2) ω = -1 ∧
      ((appCondDevModel eps0 kappa (1 / 2) ω : ℂ) + Complex.I * omegaEpsDev eps0 kappa (1 / 2) ω) = (appCondDevModel eps0 kappa (1 / 2) ω : ℂ) * (1 + Complex.I) ∧
      ((appCondDevModel eps0 kappa (-1 / 2) ω : ℂ) + Complex.I * omegaEpsDev eps0 kappa (-1 / 2) ω) = (appCondDevModel eps0 kappa (-1 / 2) ω : ℂ) * (1 - Complex.I) ∧
      Complex.arg ((appCondDevModel eps0 kappa (1 / 2) ω : ℂ) + Complex.I * omegaEpsDev eps0 kappa (1 / 2) ω) = Real.pi / 4 ∧
      Complex.arg ((appCondDevModel eps0 kappa (-1 / 2) ω : ℂ) + Complex.I * omegaEpsDev eps0 kappa (-1 / 2) ω) = 3 * Real.pi / 4 := by sorry

end Arxiv1801_00461
