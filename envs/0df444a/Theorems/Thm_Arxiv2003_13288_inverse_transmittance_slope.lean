-- Prove2me | Theorems.Thm_Arxiv2003_13288_inverse_transmittance_slope
-- name    : Arxiv2003_13288.inverse_transmittance_slope
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T09:07:55.044179+00:00
-- url     : https://prove2.me/theorems/d92ff0cf-2964-4a97-a44f-ef1b77e836ca
-- title:
--   Eq. (108): inverse total transmittance is linear in thickness (as proved)
-- statement:
--   Let $l_{\mathrm{tr}}>0$ and $\bar R\ge0$, let $z_e=\tfrac23\bar Rl_{\mathrm{tr}}$ (eq. 59), and let $T(L)=(l_{\mathrm{tr}}+z_e)/(L+2z_e)$ be the total transmittance of a slab of thickness $L>0$ given by Ohm's law (eq. 58). Then:
--
--   1. (eq. 108) $\displaystyle T(L)^{-1}=\frac{L}{l_{\mathrm{tr}}+z_e}+\frac{2z_e}{l_{\mathrm{tr}}+z_e}$ for every $L>0$;
--   2. for any two thicknesses $L_1\ne L_2$, the slope of $T^{-1}$ against $L$ is
--   $$\frac{T(L_2)^{-1}-T(L_1)^{-1}}{L_2-L_1}=\frac{1}{l_{\mathrm{tr}}(1+2\bar R/3)},$$
--   so that
--   $$l_{\mathrm{tr}}=\frac{L_2-L_1}{(1+2\bar R/3)\big(T(L_2)^{-1}-T(L_1)^{-1}\big)}.$$
--
--   **Formalization Note** The paper says that $l_{\mathrm{tr}}$ is obtained from the slope. The slope is $1/(l_{\mathrm{tr}}+z_e)$, not $1/l_{\mathrm{tr}}$, so the statement includes the factor $1+2\bar R/3$ that the recovery of $l_{\mathrm{tr}}$ requires.
-- source:
--   B. X. Wang and C. Y. Zhao, The dependent scattering effect on radiative properties of micro/nanoscale discrete disordered media, arXiv:2003.13288v1 (2020), claim c016; Sec. 5.2, eq. (108) and following sentence, with eqs. (58)-(59) of Sec. 3.4.2, PDF pp. 40, 81

import Mathlib
import Definitions.Def_Arxiv2003_13288_Basic

open MeasureTheory Filter Topology

namespace Arxiv2003_13288

theorem inverse_transmittance_slope (ltr Rbar : ℝ) (hltr : 0 < ltr) (hR : 0 ≤ Rbar) :
    (∀ L : ℝ, 0 < L →
      (ohmTransmittance ltr (extrapLength Rbar ltr) L)⁻¹ =
        L / (ltr + extrapLength Rbar ltr) + 2 * extrapLength Rbar ltr / (ltr + extrapLength Rbar ltr)) ∧
    (∀ L1 L2 : ℝ, 0 < L1 → 0 < L2 → L1 ≠ L2 →
      ((ohmTransmittance ltr (extrapLength Rbar ltr) L2)⁻¹ -
          (ohmTransmittance ltr (extrapLength Rbar ltr) L1)⁻¹) / (L2 - L1) =
        1 / (ltr * (1 + 2 * Rbar / 3)) ∧
      ltr = (L2 - L1) / ((1 + 2 * Rbar / 3) *
        ((ohmTransmittance ltr (extrapLength Rbar ltr) L2)⁻¹ -
          (ohmTransmittance ltr (extrapLength Rbar ltr) L1)⁻¹))) := by sorry

end Arxiv2003_13288
