-- Prove2me | Theorems.Thm_Arxiv1906_02603_burr_snr
-- name    : Arxiv1906_02603.burr_snr
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T06:45:24.675799+00:00
-- url     : https://prove2.me/theorems/86e19daa-204b-4b37-90b1-d23e12ba5a5c
-- title:
--   Eq. (13) (as proved): the signal-to-noise ratio of the normalized histogram
-- statement:
--   Let $\lambda>0$ and $b>2$. The density of eq. (10) has positive variance $\sigma_A^2=\langle A^2\rangle-\langle A\rangle^2$, and its signal-to-noise ratio is
--
--   $$\mathrm{SNR}=\frac{\langle A\rangle}{\sigma_A}=\frac{\Gamma(-\tfrac32+b)}{\sqrt{4(b-2)\Gamma(b-2)^2/\pi-\Gamma(-\tfrac32+b)^2}},$$
--
--   which does not depend on $\lambda$.
--
--   **Formalization Note** This is eq. (13) as it follows from eqs. (11)-(12). The printed eq. (13) has $\Gamma(-\tfrac32+b)$ without the square in the denominator; that version is false (at $b=3.4$ it gives $1.447$, the true SNR is $1.391$). The paper does not restate $b>2$ for eq. (13); it is needed for a finite variance.
-- source:
--   K. J. Parker, The first order statistics of backscatter from the fractal branching vasculature, arXiv:1906.02603v3 (2019), claim c008; Section II, eq. (13), PDF p. 12 (printed denominator lacks the square on the last Gamma; stated as derived from eqs. (11)-(12))

import Mathlib
import Definitions.Def_Arxiv1906_02603_Basic

open MeasureTheory Filter Topology Set

namespace Arxiv1906_02603

theorem burr_snr (lam b : ℝ) (hlam : 0 < lam) (hb : 2 < b) :
    0 < burrMoment lam b 2 - burrMoment lam b 1 ^ 2 ∧
    burrSNR lam b = Real.Gamma (-3 / 2 + b) /
      Real.sqrt (4 * (b - 2) * Real.Gamma (b - 2) ^ 2 / Real.pi - Real.Gamma (-3 / 2 + b) ^ 2) := by sorry

end Arxiv1906_02603
