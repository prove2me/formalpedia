-- Prove2me | Theorems.Thm_Arxiv1801_00461_kramers_kronig_admittance
-- name    : Arxiv1801_00461.kramers_kronig_admittance
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:11:05.788368+00:00
-- url     : https://prove2.me/theorems/cf16481b-cf18-4d60-8f6d-9ce24f14e2a9
-- title:
--   Eqs. (29)-(30): Hilbert-transform relations for the admittance variation
-- statement:
--   Let $\varepsilon_o>0$, let $\chi$ be integrable on $(0,\infty)$ with $\omega\bar\Delta\varepsilon(\omega)\to0$ as $|\omega|\to\infty$, and let the conductivity deviation kernel $d=\sigma_\infty\bar\Delta_e$ be integrable on $(0,\infty)$. Let $\sigma_\infty(\omega)$ be any asymptote, $\sigma_e=\sigma_\infty(\omega)+\bar\Delta\sigma_e$, $\gamma=\sigma_e+i\omega\varepsilon$, $\gamma_\infty=\sigma_\infty(\omega)+i\omega\varepsilon_o$ and $\bar\Delta\gamma=\gamma-\gamma_\infty$. Then for every real $\omega$ (eq. (29))
--
--   $$\bar\Delta\gamma'=\bar\Delta\sigma_e'-\mathcal H(\omega\bar\Delta\varepsilon'),\qquad\bar\Delta\gamma''=\omega\bar\Delta\varepsilon'+\mathcal H(\bar\Delta\sigma_e'),$$
--
--   and (eq. (30))
--
--   $$\bar\Delta\gamma''=\mathcal H(\bar\Delta\gamma'),\qquad\bar\Delta\gamma'=-\mathcal H(\bar\Delta\gamma''),$$
--
--   with the principal values in (30) existing.
--
--   The admittance variation obeys the same Hilbert relations as its two constituents.
--
--   **Formalization Note** The paper cites eqs. (16) and (25) for (29); the conductivity relation it uses is eq. (26).
-- source:
--   Bédard and Destexhe, Kramers-Kronig relations and the properties of conductivity and permittivity in heterogeneous media, arXiv:1801.00461v1 (2018), claim c028; Sec. 2.4, eqs. (27)-(30), PDF p. 10

import Mathlib
import Definitions.Def_Arxiv1801_00461_Basic

open MeasureTheory Filter Topology

namespace Arxiv1801_00461

theorem kramers_kronig_admittance (sigInf : ℝ → ℂ) (dsig : ℝ → ℝ) (hdsig : IntegrableOn dsig (Set.Ioi 0))
    (eps0 : ℝ) (heps0 : 0 < eps0) (chi : ℝ → ℝ) (hchi : IntegrableOn chi (Set.Ioi 0))
    (hdecay : Tendsto (fun a : ℝ => (a : ℂ) * permDev eps0 chi a) (cocompact ℝ) (𝓝 0)) :
    (∀ ω : ℝ, (admDev sigInf dsig eps0 chi ω).re =
        (condDev dsig ω).re - hilbert (fun a => a * (permDev eps0 chi a).re) ω ∧
      (admDev sigInf dsig eps0 chi ω).im =
        ω * (permDev eps0 chi ω).re + hilbert (fun a => (condDev dsig a).re) ω) ∧
    (∀ ω : ℝ, HasHilbert (fun a => (admDev sigInf dsig eps0 chi a).re) ω (admDev sigInf dsig eps0 chi ω).im ∧
      HasHilbert (fun a => (admDev sigInf dsig eps0 chi a).im) ω (-(admDev sigInf dsig eps0 chi ω).re)) := by sorry

end Arxiv1801_00461
