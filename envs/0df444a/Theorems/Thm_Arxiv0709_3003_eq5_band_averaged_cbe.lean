-- Prove2me | Theorems.Thm_Arxiv0709_3003_eq5_band_averaged_cbe
-- name    : Arxiv0709_3003.eq5_band_averaged_cbe
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T09:22:15.744455+00:00
-- url     : https://prove2.me/theorems/82d8e6e0-2060-433c-9ff0-57b9f1a67bb7
-- title:
--   Eq. (5): band-averaged normalized coherent backscattering enhancement
-- statement:
--   Let $N\ge1$ modes have intensity $s>0$, let the wave speed be $c>0$, and let the band $[f-\Delta f/2,f+\Delta f/2]$ have width $\Delta f>0$ and lie in the positive frequencies ($\Delta f/2<f$). Let the source-source correlation coefficient of every mode at frequency $f'$ and separation $r$ be $J_0(2\pi f'r/c)$. Then the normalised CBE of Eq. (2), averaged over the band, takes the theoretical form
--
--   $$\overline{\mathrm{CBE}}(r)=\frac1{\Delta f}\int_{f-\Delta f/2}^{f+\Delta f/2}\Big(1+2J_0^2\Big(\frac{2\pi f'}{c}r\Big)\Big)\,df'\qquad(r\in\mathbb{R}).$$
--
--   In particular $\overline{\mathrm{CBE}}(0)=3$ and $\overline{\mathrm{CBE}}(r)\to1$ as $r\to\infty$.
--
--   **Formalization Note** The paper writes both the integration variable and the band centre as $f$; here the integration variable is $f'$. The consequences at $r=0$ and $r\to\infty$ are not printed in the paper. They are recorded in the claim file for Eq. (5), and the paper's introduction gives the value three for closed cavities. The hypothesis $\Delta f/2<f$ is the experiment's setting ($\Delta f/f=50\%$).
-- source:
--   Larose, Lobkis and Weaver, Coherent backscattering of ultrasound without a source, arXiv:0709.3003v1 (2007), claim c004; first experiment, Eq. (5), PDF p. 4

import Mathlib
import Definitions.Def_Arxiv0709_3003_Basic

open MeasureTheory ProbabilityTheory Filter Topology

namespace Arxiv0709_3003

theorem eq5_band_averaged_cbe (N : ℕ) (hN : 0 < N) (s c f bw : ℝ) (hs : 0 < s) (hc : 0 < c)
    (hbw : 0 < bw) (hband : bw / 2 < f) :
    (∀ r : ℝ, cbeBandAvg N s c f bw r =
      (1 / bw) * ∫ f' in (f - bw / 2)..(f + bw / 2),
        (1 + 2 * besselJ0 (2 * Real.pi * f' * r / c) ^ 2)) ∧
    cbeBandAvg N s c f bw 0 = 3 ∧
    Tendsto (fun r => cbeBandAvg N s c f bw r) atTop (𝓝 1) := by sorry

end Arxiv0709_3003
