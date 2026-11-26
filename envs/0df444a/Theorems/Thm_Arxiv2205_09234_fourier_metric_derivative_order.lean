-- Prove2me | Theorems.Thm_Arxiv2205_09234_fourier_metric_derivative_order
-- name    : Arxiv2205_09234.fourier_metric_derivative_order
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T15:50:53.969167+00:00
-- url     : https://prove2.me/theorems/342ad55c-80bc-4ae5-961e-2ffce724107b
-- title:
--   Section 2.1 (after eq. (1)): $\mathcal L_{2,2n}^2$ is the energy of the $n$-th derivative (integer-order case)
-- statement:
--   Let $d_m,d_o:\mathbb{R}\to\mathbb{R}$ be Schwartz functions and let $n\ge0$ be an integer. Then the Fourier-based metric with $p=2$ and $\alpha=2n$ measures the energy of the $n$-th derivative of the residual $d_m-d_o$:
--
--   $$\mathcal L_{2,2n}(d_m,d_o)^2=\int_{\mathbb{R}}|\omega|^{2n}\,|\hat d_m(\omega)-\hat d_o(\omega)|^2\,d\omega=2\pi\int_{\mathbb{R}}\big|(d_m-d_o)^{(n)}(t)\big|^2\,dt.$$
--
--   This makes precise the paper's remark that $\alpha$ controls how much a derivative of a given order (here $\alpha/2=n$) of the waveform contributes to the mismatch; $n=0$ is the Plancherel identity.
--
--   **Formalization Note** Only the case $p=2$, $\alpha=2n$ with $n\in\mathbb{N}$ is stated. The paper gives no definition of a fractional derivative or integral, so the readings for non-even $\alpha$ and for $\alpha<0$ ("integration") are not stated. Schwartz regularity is assumed so that all integrals exist.
-- source:
--   Izzatullah and Alkhalifah, omega-FWI: Robust full-waveform inversion with Fourier-based metric, arXiv:2205.09234v1 (2022), claim c001; Section 2.1, eq. (1) and the paragraph after it, PDF p. 2

import Mathlib
import Definitions.Def_Arxiv2205_09234_Basic

open MeasureTheory Matrix

namespace Arxiv2205_09234

theorem fourier_metric_derivative_order (dm dobs : SchwartzMap ℝ ℝ) (n : ℕ) :
    fourierMetric 2 (2 * (n : ℝ)) dm dobs ^ 2 =
      2 * Real.pi * ∫ t : ℝ, (iteratedDeriv n (fun s => dm s - dobs s) t) ^ 2 := by sorry

end Arxiv2205_09234
