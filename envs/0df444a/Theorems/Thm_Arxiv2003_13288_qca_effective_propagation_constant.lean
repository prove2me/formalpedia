-- Prove2me | Theorems.Thm_Arxiv2003_13288_qca_effective_propagation_constant
-- name    : Arxiv2003_13288.qca_effective_propagation_constant
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T09:06:15.688897+00:00
-- url     : https://prove2.me/theorems/179cc6df-089b-403a-bd3d-a2c381a58914
-- title:
--   Eq. (81): effective propagation constant under the QCA
-- statement:
--   Let $n_0,k>0$, let $t_0\ne0$, let $h_2$ be a pair correlation function, and let $\Sigma_{\mathrm{QCA}}$ be the QCA self-energy of eq. (80). If $K^2=k^2\varepsilon_{\mathrm{eff}}$ with $\varepsilon_{\mathrm{eff}}=1-\Sigma_{\mathrm{QCA}}/k^2$ (eq. 35), then
--
--   $$K^2=k^2-\frac{1}{1/(n_0t_0)+1/(3k^2)+2\int_0^\infty dr\,r\,e^{ikr}[g_2(r)-1]/3}.$$
-- source:
--   B. X. Wang and C. Y. Zhao, The dependent scattering effect on radiative properties of micro/nanoscale discrete disordered media, arXiv:2003.13288v1 (2020), claim c008; Sec. 4.2.4, eqs. (35), (80), (81), PDF p. 55

import Mathlib
import Definitions.Def_Arxiv2003_13288_Basic

open MeasureTheory Filter Topology

namespace Arxiv2003_13288

theorem qca_effective_propagation_constant (n0 k : ℝ) (hn0 : 0 < n0) (hk : 0 < k) (t0 : ℂ)
    (ht0 : t0 ≠ 0) (h2 : ℝ → ℝ) (K : ℂ)
    (hK : K ^ 2 = (k : ℂ) ^ 2 * effPermittivity k (qcaSelfEnergy n0 k t0 h2)) :
    K ^ 2 = (k : ℂ) ^ 2 - 1 / (1 / (n0 * t0) + 1 / (3 * (k : ℂ) ^ 2) + 2 * corrIntegral k h2 / 3) := by sorry

end Arxiv2003_13288
