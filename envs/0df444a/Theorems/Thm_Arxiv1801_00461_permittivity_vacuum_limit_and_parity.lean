-- Prove2me | Theorems.Thm_Arxiv1801_00461_permittivity_vacuum_limit_and_parity
-- name    : Arxiv1801_00461.permittivity_vacuum_limit_and_parity
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:07:29.527821+00:00
-- url     : https://prove2.me/theorems/e44a4ac1-1ba3-4f5e-b907-ee85e4d4b03d
-- title:
--   Eq. (11): the permittivity tends to that of vacuum, with even real and odd imaginary part
-- statement:
--   Let $\varepsilon_o>0$ and let the susceptibility kernel $\chi:(0,\infty)\to\mathbb R$ be integrable. Put $\varepsilon(\omega)=\varepsilon_o\big[1+\int_0^\infty\chi(\tau)e^{-i\omega\tau}d\tau\big]$ for real $\omega$. Then
--
--   $$\bar\Delta\varepsilon(\omega)=\varepsilon(\omega)-\varepsilon_o=\int_0^\infty\varepsilon_o\chi(\tau)e^{-i\omega\tau}d\tau\ \xrightarrow[\omega\to+\infty]{}\ 0,$$
--
--   so $\varepsilon(\omega)\to\varepsilon_o$. Moreover $\operatorname{Re}\bar\Delta\varepsilon$ is even and $\operatorname{Im}\bar\Delta\varepsilon$ is odd in $\omega$.
--
--   The permittivity therefore tends to that of vacuum at infinite frequency.
--
--   **Formalization Note** The paper allows $\chi$ to be any function or distribution and assumes only that the Fourier transform exists (footnote 3). The statement takes $\chi$ to be a Lebesgue-integrable function on $(0,\infty)$, which is what the existence of the integral (11) means for a function. If $\chi$ contained a $\delta$-part, the limit would fail.
-- source:
--   Bédard and Destexhe, Kramers-Kronig relations and the properties of conductivity and permittivity in heterogeneous media, arXiv:1801.00461v1 (2018), claim c001; Sec. 2.2.1, eqs. (10)-(11) and the paragraph after (11), PDF pp. 4-5

import Mathlib
import Definitions.Def_Arxiv1801_00461_Basic

open MeasureTheory Filter Topology

namespace Arxiv1801_00461

theorem permittivity_vacuum_limit_and_parity (eps0 : ℝ) (heps0 : 0 < eps0) (chi : ℝ → ℝ)
    (hchi : IntegrableOn chi (Set.Ioi 0)) :
    (∀ ω : ℝ, permittivity eps0 chi ω - eps0 = permDev eps0 chi ω) ∧
    Tendsto (fun ω : ℝ => permDev eps0 chi ω) atTop (𝓝 0) ∧
    Tendsto (fun ω : ℝ => permittivity eps0 chi ω) atTop (𝓝 (eps0 : ℂ)) ∧
    (∀ ω : ℝ, (permDev eps0 chi ((-ω : ℝ) : ℂ)).re = (permDev eps0 chi ω).re) ∧
    (∀ ω : ℝ, (permDev eps0 chi ((-ω : ℝ) : ℂ)).im = -(permDev eps0 chi ω).im) := by sorry

end Arxiv1801_00461
