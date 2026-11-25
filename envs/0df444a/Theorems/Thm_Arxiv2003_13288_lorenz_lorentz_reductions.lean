-- Prove2me | Theorems.Thm_Arxiv2003_13288_lorenz_lorentz_reductions
-- name    : Arxiv2003_13288.lorenz_lorentz_reductions
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T09:00:50.342751+00:00
-- url     : https://prove2.me/theorems/621f0ce6-20e1-43ae-aa5f-b1734406ab14
-- title:
--   Eqs. (65)-(68): the Lorenz-Lorentz self-energy, Clausius-Mossotti and Maxwell-Garnett
-- statement:
--   Let $n_0>0$, $k>0$, let $\alpha\in\mathbb C$ be the dipole polarizability with $1-n_0\alpha/3\ne0$, and let $t_0=-k^2\alpha$. Then:
--
--   1. (eq. 65) $\displaystyle\Sigma_{\mathrm{LLR}}=\frac{n_0t_0}{1+n_0t_0/(3k^2)}=-\frac{n_0\alpha k^2}{1-n_0\alpha/3}$;
--   2. (eq. 66) if $|n_0t_0/(3k^2)|<1$, then $\displaystyle\Sigma_{\mathrm{LLR}}=n_0t_0\sum_{m\ge0}\Big(-\frac13\Big)^m\Big(\frac{n_0t_0}{k^2}\Big)^m$;
--   3. (eq. 67) with $\varepsilon_{\mathrm{eff}}=1-\Sigma_{\mathrm{LLR}}/k^2$, $\dfrac{\varepsilon_{\mathrm{eff}}-1}{\varepsilon_{\mathrm{eff}}+2}=\dfrac13n_0\alpha$ (Clausius-Mossotti);
--   4. (eq. 68) if $\alpha=\alpha_{\mathrm{ES}}=4\pi a^3(\varepsilon_p-1)/(\varepsilon_p+2)$ with $a>0$ and $\varepsilon_p\ne-2$, then $\dfrac{\varepsilon_{\mathrm{eff}}-1}{\varepsilon_{\mathrm{eff}}+2}=f_v\dfrac{\varepsilon_p-1}{\varepsilon_p+2}$ with $f_v=\tfrac43\pi a^3n_0$ (Maxwell-Garnett).
--
--   **Formalization Note** The convergence condition $|n_0t_0/(3k^2)|<1$ of the geometric series in item 2 is not stated in the paper; it is added because the series diverges otherwise.
-- source:
--   B. X. Wang and C. Y. Zhao, The dependent scattering effect on radiative properties of micro/nanoscale discrete disordered media, arXiv:2003.13288v1 (2020), claim c015; Sec. 4.2.2, eqs. (65)-(68), PDF pp. 50-51

import Mathlib
import Definitions.Def_Arxiv2003_13288_Basic

open MeasureTheory Filter Topology

namespace Arxiv2003_13288

theorem lorenz_lorentz_reductions (n0 k : ℝ) (hn0 : 0 < n0) (hk : 0 < k) (alpha : ℂ)
    (hden : 1 - n0 * alpha / 3 ≠ 0) :
    llrSelfEnergy n0 k (dipoleT k alpha) = -(n0 * alpha * k ^ 2) / (1 - n0 * alpha / 3) ∧
    (‖n0 * dipoleT k alpha / (3 * k ^ 2)‖ < 1 →
      HasSum (fun m : ℕ => n0 * dipoleT k alpha * ((-1 / 3 : ℂ) ^ m * (n0 * dipoleT k alpha / k ^ 2) ^ m))
        (llrSelfEnergy n0 k (dipoleT k alpha))) ∧
    (effPermittivity k (llrSelfEnergy n0 k (dipoleT k alpha)) - 1) /
        (effPermittivity k (llrSelfEnergy n0 k (dipoleT k alpha)) + 2) = n0 * alpha / 3 ∧
    (∀ (a : ℝ) (epsP : ℂ), 0 < a → epsP + 2 ≠ 0 → alpha = alphaES a epsP →
      (effPermittivity k (llrSelfEnergy n0 k (dipoleT k alpha)) - 1) /
          (effPermittivity k (llrSelfEnergy n0 k (dipoleT k alpha)) + 2) =
        volFraction n0 a * (epsP - 1) / (epsP + 2)) := by sorry

end Arxiv2003_13288
