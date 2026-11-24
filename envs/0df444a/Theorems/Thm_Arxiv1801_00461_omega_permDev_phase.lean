-- Prove2me | Theorems.Thm_Arxiv1801_00461_omega_permDev_phase
-- name    : Arxiv1801_00461.omega_permDev_phase
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:08:59.037248+00:00
-- url     : https://prove2.me/theorems/045e4ab7-bde0-44f8-ab8b-b555216dbc61
-- title:
--   Eq. (17): the phase of $\omega\bar\Delta\varepsilon$ is fixed by its real or its imaginary part
-- statement:
--   Under the hypotheses of eq. (16) ($\varepsilon_o>0$, $\chi$ integrable on $(0,\infty)$, $\omega\bar\Delta\varepsilon(\omega)\to0$ as $|\omega|\to\infty$), write $G(\omega)=\omega\bar\Delta\varepsilon(\omega)$ for real $\omega$. Then:
--
--   1. (eq. (17)) $G=\omega\bar\Delta\varepsilon'+i\,\mathcal H[\omega\bar\Delta\varepsilon']=-\mathcal H[\omega\bar\Delta\varepsilon'']+i\,\omega\bar\Delta\varepsilon''$ at every $\omega$;
--   2. wherever $\omega\bar\Delta\varepsilon'(\omega)\ne0$, the phase $\phi=\arg G(\omega)$ satisfies
--   $$\tan\phi=\frac{\mathcal H[\omega\bar\Delta\varepsilon'](\omega)}{\omega\bar\Delta\varepsilon'(\omega)}=-\frac{\omega\bar\Delta\varepsilon''(\omega)}{\mathcal H[\omega\bar\Delta\varepsilon''](\omega)};$$
--   3. the phase is determined by either part: if a second susceptibility $\chi'$ satisfying the same hypotheses gives the same $\omega\bar\Delta\varepsilon'$ on all of $\mathbb R$, or the same $\omega\bar\Delta\varepsilon''$, then the two phases agree at every frequency.
--
--   **Formalization Note** The phase is the principal argument $\arg\in(-\pi,\pi]$. The tangent formula is stated only where the real part is non-zero, because the paper's quotient is undefined elsewhere.
-- source:
--   Bédard and Destexhe, Kramers-Kronig relations and the properties of conductivity and permittivity in heterogeneous media, arXiv:1801.00461v1 (2018), claim c004; Sec. 2.2.2, eq. (17) and the phase relation after it, PDF p. 7

import Mathlib
import Definitions.Def_Arxiv1801_00461_Basic

open MeasureTheory Filter Topology

namespace Arxiv1801_00461

theorem omega_permDev_phase (eps0 : ℝ) (heps0 : 0 < eps0) (chi : ℝ → ℝ)
    (hchi : IntegrableOn chi (Set.Ioi 0))
    (hdecay : Tendsto (fun a : ℝ => (a : ℂ) * permDev eps0 chi a) (cocompact ℝ) (𝓝 0)) :
    (∀ ω : ℝ,
      (ω : ℂ) * permDev eps0 chi ω =
          ((ω * (permDev eps0 chi ω).re : ℝ) : ℂ) +
            Complex.I * hilbert (fun a => a * (permDev eps0 chi a).re) ω ∧
      (ω : ℂ) * permDev eps0 chi ω =
          ((-hilbert (fun a => a * (permDev eps0 chi a).im) ω : ℝ) : ℂ) +
            Complex.I * ((ω * (permDev eps0 chi ω).im : ℝ) : ℂ)) ∧
    (∀ ω : ℝ, ω * (permDev eps0 chi ω).re ≠ 0 →
      Real.tan (Complex.arg ((ω : ℂ) * permDev eps0 chi ω)) =
          hilbert (fun a => a * (permDev eps0 chi a).re) ω / (ω * (permDev eps0 chi ω).re) ∧
      Real.tan (Complex.arg ((ω : ℂ) * permDev eps0 chi ω)) =
          -(ω * (permDev eps0 chi ω).im) / hilbert (fun a => a * (permDev eps0 chi a).im) ω) ∧
    (∀ chi' : ℝ → ℝ, IntegrableOn chi' (Set.Ioi 0) →
      Tendsto (fun a : ℝ => (a : ℂ) * permDev eps0 chi' a) (cocompact ℝ) (𝓝 0) →
      ((∀ a : ℝ, a * (permDev eps0 chi' a).re = a * (permDev eps0 chi a).re) ∨
        (∀ a : ℝ, a * (permDev eps0 chi' a).im = a * (permDev eps0 chi a).im)) →
      ∀ ω : ℝ, Complex.arg ((ω : ℂ) * permDev eps0 chi' ω) =
        Complex.arg ((ω : ℂ) * permDev eps0 chi ω)) := by sorry

end Arxiv1801_00461
