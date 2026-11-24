-- Prove2me | Theorems.Thm_Arxiv1801_00461_kramers_kronig_omega_permittivity
-- name    : Arxiv1801_00461.kramers_kronig_omega_permittivity
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:08:30.300168+00:00
-- url     : https://prove2.me/theorems/8a5b56ce-fbcb-4e50-8805-0e92742e2c6b
-- title:
--   Eqs. (15)-(16): Hilbert-transform relations for $\omega\bar\Delta\varepsilon$
-- statement:
--   Let $\varepsilon_o>0$, let $\chi:(0,\infty)\to\mathbb R$ be integrable, and let $\bar\Delta\varepsilon(\omega)=\int_0^\infty\varepsilon_o\chi(\tau)e^{-i\omega\tau}d\tau$. Assume, as the paper postulates after eq. (15), that $\omega_a\bar\Delta\varepsilon(\omega_a)\to0$ as $|\omega_a|\to\infty$ on the real axis. Write $\bar\Delta\varepsilon=\bar\Delta\varepsilon'+i\bar\Delta\varepsilon''$. Then for every real $\omega$
--
--   $$\omega\,\bar\Delta\varepsilon''(\omega)=\mathcal H(\omega\bar\Delta\varepsilon')(\omega)=\frac1\pi\,⨍_{-\infty}^{\infty}\frac{\omega_a\bar\Delta\varepsilon'(\omega_a)}{\omega_a-\omega}d\omega_a,$$
--   $$\omega\,\bar\Delta\varepsilon'(\omega)=-\mathcal H(\omega\bar\Delta\varepsilon'')(\omega)=-\frac1\pi\,⨍_{-\infty}^{\infty}\frac{\omega_a\bar\Delta\varepsilon''(\omega_a)}{\omega_a-\omega}d\omega_a,$$
--
--   and both principal values exist.
--
--   These are the Kramers–Kronig relations for $\omega\bar\Delta\varepsilon$, with the sign of a function holomorphic in the lower half-plane.
--
--   **Formalization Note** The principal value is taken with the coupled truncation $(\delta,1/\delta)$ of Fig. 1. Eq. (15), $\omega\bar\Delta\varepsilon=-\frac1{\pi i}⨍\frac{\omega_a\bar\Delta\varepsilon(\omega_a)}{\omega_a-\omega}d\omega_a$, is the combination of the two displayed relations. Its printed integrand has $\omega$ where $\omega_a$ is meant.
-- source:
--   Bédard and Destexhe, Kramers-Kronig relations and the properties of conductivity and permittivity in heterogeneous media, arXiv:1801.00461v1 (2018), claim c003; Sec. 2.2.2, eqs. (14)-(16) and the remarks after (16), PDF pp. 6-7

import Mathlib
import Definitions.Def_Arxiv1801_00461_Basic

open MeasureTheory Filter Topology

namespace Arxiv1801_00461

theorem kramers_kronig_omega_permittivity (eps0 : ℝ) (heps0 : 0 < eps0) (chi : ℝ → ℝ)
    (hchi : IntegrableOn chi (Set.Ioi 0))
    (hdecay : Tendsto (fun a : ℝ => (a : ℂ) * permDev eps0 chi a) (cocompact ℝ) (𝓝 0))
    (ω : ℝ) :
    HasHilbert (fun a => a * (permDev eps0 chi a).re) ω (ω * (permDev eps0 chi ω).im) ∧
    HasHilbert (fun a => a * (permDev eps0 chi a).im) ω (-(ω * (permDev eps0 chi ω).re)) := by sorry

end Arxiv1801_00461
