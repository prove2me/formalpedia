-- Prove2me | Theorems.Thm_Arxiv0709_3003_eq5_single_frequency_cbe
-- name    : Arxiv0709_3003.eq5_single_frequency_cbe
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:21:51.267901+00:00
-- url     : https://prove2.me/theorems/46f55ac6-12a7-4c0d-8d66-edf90d491f44
-- title:
--   Eq. (5) at a single frequency (as proved): the normalized CBE is 1 + 2 J0^2
-- statement:
--   Let $N\ge1$ modes have intensity $s>0$, let the wave speed be $c>0$ and the frequency $f>0$, and let the source-source correlation coefficient of every mode be $J_0(2\pi fr/c)$ at separation $r$. Then the model mean squared correlation tends to $3Ns^4$ as $r\to\infty$, and for every $r\in\mathbb{R}$
--
--   $$\mathrm{CBE}_{\rm spatial}(r)=\frac{\langle C_{ij}^2(r)\rangle}{\langle C_{ij}^2(r\gg\lambda)\rangle}=1+2J_0^2\Big(\frac{2\pi f}{c}r\Big).$$
--
--   **Formalization Note** This is the integrand of Eq. (5). The paper passes from Eq. (4) to Eq. (5) without writing it at one frequency. The limit value $3Ns^4$ is the one the Gaussian expansion gives; the printed Eq. (4) would give $\langle u^2\rangle^4$ (see Eq. (4) as proved). The limit $r\to\infty$ stands for $r\gg\lambda$.
-- source:
--   Larose, Lobkis and Weaver, Coherent backscattering of ultrasound without a source, arXiv:0709.3003v1 (2007), claim c004; first experiment, Eqs. (2), (4), (5), PDF pp. 3-4

import Mathlib
import Definitions.Def_Arxiv0709_3003_Basic

open MeasureTheory ProbabilityTheory Filter Topology

namespace Arxiv0709_3003

theorem eq5_single_frequency_cbe (N : ℕ) (hN : 0 < N) (s c f r : ℝ) (hs : 0 < s) (hc : 0 < c)
    (hf : 0 < f) :
    Tendsto (fun r' => meanSqCorr N s c f r') atTop (𝓝 (3 * N * s ^ 4)) ∧
      cbeSpatial N s c f r = 1 + 2 * besselJ0 (2 * Real.pi * f * r / c) ^ 2 := by sorry

end Arxiv0709_3003
