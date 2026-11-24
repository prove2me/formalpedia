-- Prove2me | Theorems.Thm_Arxiv1801_00461_apparent_parameters_hilbert_pair
-- name    : Arxiv1801_00461.apparent_parameters_hilbert_pair
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:13:12.246801+00:00
-- url     : https://prove2.me/theorems/4f575280-a768-41a2-8aa4-b535e21c92e9
-- title:
--   Eqs. (35)-(36): the apparent conductivity and permittivity are a Hilbert pair
-- statement:
--   Under the hypotheses of eq. (30), assume also that the asymptote is the transform of a real kernel, $\sigma_\infty(-\omega)=\overline{\sigma_\infty(\omega)}$. Define the apparent conductivity $\sigma_A=\gamma'=\sigma_e'-\omega\varepsilon''$ (eq. (35)) and the apparent permittivity by $\omega\varepsilon_A=\gamma''=\omega\varepsilon'+\sigma_e''$ (eq. (36)). Write $\bar\Delta\sigma_A=\sigma_A-\operatorname{Re}\gamma_\infty$ and $\omega\bar\Delta\varepsilon_A=\omega\big(\varepsilon_A-\operatorname{Im}\gamma_\infty/\omega\big)$ for the deviations from the high-frequency values. Then for every real $\omega$
--
--   $$\omega\bar\Delta\varepsilon_A=\mathcal H(\bar\Delta\sigma_A),\qquad\bar\Delta\sigma_A=-\mathcal H(\omega\bar\Delta\varepsilon_A),$$
--
--   with the principal values existing, and $\sigma_A$ and $\varepsilon_A$ are even functions of $\omega$.
--
--   Knowing one apparent parameter at all frequencies therefore determines the other.
--
--   **Formalization Note** $\varepsilon_A=\gamma''/\omega$ is used for $\omega\ne0$; at $\omega=0$ both sides of each identity are $0$. The sentence that introduces these relations is garbled in the source. The plane-capacitor interpretation (Fig. 2) is not a mathematical statement and is not included.
-- source:
--   Bédard and Destexhe, Kramers-Kronig relations and the properties of conductivity and permittivity in heterogeneous media, arXiv:1801.00461v1 (2018), claim c011; Sec. 2.4, eqs. (35)-(36) and the paragraph after (36), PDF p. 11

import Mathlib
import Definitions.Def_Arxiv1801_00461_Basic

open MeasureTheory Filter Topology

namespace Arxiv1801_00461

theorem apparent_parameters_hilbert_pair (sigInf : ℝ → ℂ) (dsig : ℝ → ℝ) (hdsig : IntegrableOn dsig (Set.Ioi 0))
    (eps0 : ℝ) (heps0 : 0 < eps0) (chi : ℝ → ℝ) (hchi : IntegrableOn chi (Set.Ioi 0))
    (hdecay : Tendsto (fun a : ℝ => (a : ℂ) * permDev eps0 chi a) (cocompact ℝ) (𝓝 0))
    (hsigInf : ∀ ω : ℝ, sigInf (-ω) = (starRingEnd ℂ) (sigInf ω)) :
    (∀ ω : ℝ, HasHilbert (fun a => appCond sigInf dsig eps0 chi a - appCondInf sigInf eps0 a) ω
        (ω * (appPerm sigInf dsig eps0 chi ω - appPermInf sigInf eps0 ω))) ∧
    (∀ ω : ℝ, HasHilbert (fun a => a * (appPerm sigInf dsig eps0 chi a - appPermInf sigInf eps0 a)) ω
        (-(appCond sigInf dsig eps0 chi ω - appCondInf sigInf eps0 ω))) ∧
    (∀ ω : ℝ, appCond sigInf dsig eps0 chi (-ω) = appCond sigInf dsig eps0 chi ω) ∧
    (∀ ω : ℝ, appPerm sigInf dsig eps0 chi (-ω) = appPerm sigInf dsig eps0 chi ω) := by sorry

end Arxiv1801_00461
