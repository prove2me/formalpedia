-- Prove2me | Theorems.Thm_Arxiv1507_03491_local_density_smooth
-- name    : Arxiv1507_03491.local_density_smooth
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T17:39:10.15626+00:00
-- url     : https://prove2.me/theorems/b2545df9-ed22-47c5-a08d-d0b24862909c
-- title:
--   Remark 4: for $h>0$ the data and the local density are smooth on $\Gamma_0$
-- statement:
--   Let $\operatorname{Re}k>0$, $\operatorname{Im}k\ge0$, $\operatorname{Re}\alpha\ge0$, $M_0>0$ and $h>0$. Let $g=-\partial G_k(\cdot,(0,h))/\partial n-ik\alpha\,G_k(\cdot,(0,h))$ on $\Gamma$ (eq. 3.4). Let $\sigma\in C(\overline{\Gamma_0})$ solve the local integral equation (3.9), $-\tfrac12\sigma+ik\alpha S_{\Gamma_0}[\sigma]=g$ on $\Gamma_0$. Then:
--
--   1. $g\in C^\infty(\Gamma_0)$;
--   2. $\sigma\in C^{0,r}(\Gamma_0)$ for every $0<r<1$;
--   3. $\sigma\in C^\infty(\Gamma_0)$.
--
--   The smoothness of $\sigma$ inside $\Gamma_0$ is what allows the windowed density $\sigma_W=W\sigma$ to be treated as a smooth function.
--
--   **Formalization Note** $\Gamma_0$ is the open interval (Remark 3), so smoothness is asserted on the open interval only; the Hölder bound is uniform on $\Gamma_0$.
-- source:
--   Lai, Greengard and O'Neil, A new hybrid integral representation for frequency domain scattering in layered media, arXiv:1507.03491v2 (2015), claim c011; Section 5, Remark 4, PDF p. 13, with eq. (3.4) (PDF p. 9) and eq. (3.9) (PDF p. 10)

import Mathlib
import Definitions.Def_Arxiv1507_03491_Basic

open MeasureTheory Filter Topology Set
open scoped ContDiff NNReal

namespace Arxiv1507_03491

theorem local_density_smooth (k alpha : ℂ) (hk : 0 < k.re) (hk' : 0 ≤ k.im)
    (halpha : 0 ≤ alpha.re) (M0 : ℝ) (hM0 : 0 < M0) (h : ℝ) (hh : 0 < h) (sigma : ℝ → ℂ)
    (hsigma : ContinuousOn sigma (Icc (-M0) M0))
    (heq : ∀ x ∈ Ioo (-M0) M0,
      -(1 / 2) * sigma x + Complex.I * k * alpha * singleLayer k M0 sigma x 0 =
        impedanceRHS k alpha h x) :
    ContDiffOn ℝ ∞ (impedanceRHS k alpha h) (Ioo (-M0) M0) ∧
    (∀ r : ℝ≥0, 0 < r → r < 1 → ∃ C : ℝ≥0, HolderOnWith C r sigma (Ioo (-M0) M0)) ∧
    ContDiffOn ℝ ∞ sigma (Ioo (-M0) M0) := by sorry

end Arxiv1507_03491
