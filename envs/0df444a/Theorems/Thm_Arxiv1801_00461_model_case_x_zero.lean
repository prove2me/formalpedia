-- Prove2me | Theorems.Thm_Arxiv1801_00461_model_case_x_zero
-- name    : Arxiv1801_00461.model_case_x_zero
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:16:08.34844+00:00
-- url     : https://prove2.me/theorems/237850c2-d88f-40c8-bebb-0d59fb45e29b
-- title:
--   Eq. (43) (as proved): the case $x=0$ of the model (38)
-- statement:
--   Let $\varepsilon_o>0$, $\kappa\ge0$ and $\varepsilon_A=\varepsilon_o+\kappa/|\omega|^2$ (the case $x=0$). Then:
--
--   1. the truncated integral of eq. (42) tends to $0$, so $\kappa_1=0$ (eq. (43));
--   2. $\mathcal H(\bar\Delta(\omega\varepsilon_A))(\omega)=0$ for every $\omega\ne0$, so $\bar\Delta\sigma_A=0$ and the apparent conductivity does not depend on frequency;
--   3. if $\kappa>0$, the admittance variation $\bar\Delta\sigma_A+i\bar\Delta(\omega\varepsilon_A)=i\kappa/\omega$ has phase $\phi=+\pi/2$ for $\omega>0$ and $\phi=-\pi/2$ for $\omega<0$.
--
--   **Formalization Note** The paper prints $\phi=-\pi/2$ for $\omega>0$ and $\phi=+\pi/2$ for $\omega<0$. Its argument gives only $\tan\phi=\infty$, and with $\gamma=\sigma+i\omega\varepsilon$ (eq. (27)) the variation is $i\kappa/\omega$, whose argument is $+\pi/2$ for $\omega>0$. Item 3 states the value that follows. Two remarks of the paper are not included: the identification $\sigma_A=\sigma_e'(\omega\to\infty)$, which rests on the informal limits $\varepsilon''\to0$, $\varepsilon'\to\varepsilon_o$, and the formula for the phase of $\gamma$ in a resistive medium, which is a rearrangement of the definitions.
-- source:
--   Bédard and Destexhe, Kramers-Kronig relations and the properties of conductivity and permittivity in heterogeneous media, arXiv:1801.00461v1 (2018), claim c018; Sec. 3.1.2, Case x=0, eq. (43) and the following paragraph, PDF p. 14

import Mathlib
import Definitions.Def_Arxiv1801_00461_Basic

open MeasureTheory Filter Topology

namespace Arxiv1801_00461

theorem model_case_x_zero (eps0 kappa : ℝ) (heps0 : 0 < eps0) (hkappa : 0 ≤ kappa) :
    Tendsto (kernelTrunc 0) (𝓝[>] 0) (𝓝 0) ∧ kappaOne kappa 0 = 0 ∧
    (∀ ω : ℝ, ω ≠ 0 → HasHilbert (omegaEpsDev eps0 kappa 0) ω 0) ∧
    (0 < kappa → ∀ ω : ℝ, 0 < ω →
      Complex.arg ((appCondDevModel eps0 kappa 0 ω : ℂ) +
        Complex.I * omegaEpsDev eps0 kappa 0 ω) = Real.pi / 2) ∧
    (0 < kappa → ∀ ω : ℝ, ω < 0 →
      Complex.arg ((appCondDevModel eps0 kappa 0 ω : ℂ) +
        Complex.I * omegaEpsDev eps0 kappa 0 ω) = -(Real.pi / 2)) := by sorry

end Arxiv1801_00461
