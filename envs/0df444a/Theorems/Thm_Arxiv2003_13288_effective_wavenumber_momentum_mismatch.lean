-- Prove2me | Theorems.Thm_Arxiv2003_13288_effective_wavenumber_momentum_mismatch
-- name    : Arxiv2003_13288.effective_wavenumber_momentum_mismatch
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T08:54:10.026903+00:00
-- url     : https://prove2.me/theorems/17a00763-42cb-5a64-bd3f-088865e14d33
-- title:
--   Sec. 3.2.1: the effective wavenumber and the peak momentum
-- statement:
--   Let $k>0$, let $\varepsilon^\perp(p)$ be the transverse effective permittivity as a function of the momentum $p$, and let $p_{\max}\ge0$ satisfy
--
--   $$\mathrm{Re}\,\varepsilon^\perp(p_{\max})-p_{\max}^2/k^2=0.$$
--
--   Then the effective wavenumber $K^\perp=\sqrt{\varepsilon^\perp(p_{\max})}\,k$ satisfies
--
--   $$(\mathrm{Re}\,K^\perp)^2-(\mathrm{Im}\,K^\perp)^2=p_{\max}^2,$$
--
--   and if $\mathrm{Im}\,\varepsilon^\perp(p_{\max})\ne0$ then $p_{\max}<\mathrm{Re}\,K^\perp$: the real part of the effective wavenumber differs from (indeed exceeds) the peak momentum.
--
--   **Formalization Note** The paper's preceding assertion, that the transverse spectral function peaks where $\mathrm{Re}\,\varepsilon^\perp-p^2/k^2$ vanishes, is not part of the statement. It is taken as the hypothesis on $p_{\max}$; the statement is the step the paper derives from it.
-- source:
--   B. X. Wang and C. Y. Zhao, The dependent scattering effect on radiative properties of micro/nanoscale discrete disordered media, arXiv:2003.13288v1 (2020), claim c004; Sec. 3.2.1, text after eqs. (36)-(38), PDF pp. 27-28

import Mathlib
import Definitions.Def_Arxiv2003_13288_Basic

open MeasureTheory Filter Topology

namespace Arxiv2003_13288

theorem effective_wavenumber_momentum_mismatch (k : ℝ) (hk : 0 < k) (epsPerp : ℝ → ℂ)
    (pmax : ℝ) (hpmax : 0 ≤ pmax) (hpeak : (epsPerp pmax).re - pmax ^ 2 / k ^ 2 = 0) :
    (effWavenumber k (epsPerp pmax)).re ^ 2 - (effWavenumber k (epsPerp pmax)).im ^ 2 = pmax ^ 2 ∧
    ((epsPerp pmax).im ≠ 0 → pmax < (effWavenumber k (epsPerp pmax)).re) := by sorry

end Arxiv2003_13288
