-- Prove2me | Theorems.Thm_Arxiv1801_00461_apparent_parameters_special_cases
-- name    : Arxiv1801_00461.apparent_parameters_special_cases
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T04:13:38.090364+00:00
-- url     : https://prove2.me/theorems/71b4ce4e-ea14-4b95-8358-55245feb2829
-- title:
--   Sec. 2.4, properties of the apparent parameters (as proved): first and third property
-- statement:
--   Let $\sigma_e(\omega)=\sigma_\infty(\omega)+\bar\Delta\sigma_e(\omega)$, $\varepsilon(\omega)$ and the apparent parameters $\sigma_A=\sigma_e'-\omega\varepsilon''$, $\varepsilon_A=\varepsilon'+\sigma_e''/\omega$ be as in eqs. (24), (10), (35), (36). Then:
--
--   1. the apparent conductivity equals the real part of the electric conductivity at $\omega=0$, and at every frequency at which $\operatorname{Im}\varepsilon=0$;
--   2. at every frequency $\omega\ne0$ at which $\operatorname{Im}\sigma_e=0$ and $\operatorname{Im}\varepsilon=0$, the apparent parameters equal the electric parameters: $\sigma_A=\sigma_e'$ and $\varepsilon_A=\varepsilon'$.
--
--   **Formalization Note** These are the first and third of the four properties listed in the paper. They are identities of the definitions and need no hypothesis on the kernels. The second property, that $\varepsilon_A$ is infinite at $\omega=0$ when $\sigma_e''\ne0$, is not included because it is false: $\sigma_e''$ is odd and continuous, so $\sigma_e''(0)=0$, and for $d(t)=e^{-t}$ the ratio $\sigma_e''/\omega$ tends to $-1$. The fourth property is an approximation ('negligible') with no precise content.
-- source:
--   Bédard and Destexhe, Kramers-Kronig relations and the properties of conductivity and permittivity in heterogeneous media, arXiv:1801.00461v1 (2018), claim c012; Sec. 2.4, last paragraph, PDF p. 11

import Mathlib
import Definitions.Def_Arxiv1801_00461_Basic

open MeasureTheory Filter Topology

namespace Arxiv1801_00461

theorem apparent_parameters_special_cases (sigInf : ℝ → ℂ) (dsig : ℝ → ℝ) (eps0 : ℝ)
    (chi : ℝ → ℝ) :
    appCond sigInf dsig eps0 chi 0 = (condFreq sigInf dsig 0).re ∧
    (∀ ω : ℝ, (permittivity eps0 chi ω).im = 0 → appCond sigInf dsig eps0 chi ω = (condFreq sigInf dsig ω).re) ∧
    (∀ ω : ℝ, ω ≠ 0 → (condFreq sigInf dsig ω).im = 0 → (permittivity eps0 chi ω).im = 0 →
      appCond sigInf dsig eps0 chi ω = (condFreq sigInf dsig ω).re ∧ appPerm sigInf dsig eps0 chi ω = (permittivity eps0 chi ω).re) := by sorry

end Arxiv1801_00461
