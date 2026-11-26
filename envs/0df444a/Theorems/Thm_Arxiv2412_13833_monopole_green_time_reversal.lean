-- Prove2me | Theorems.Thm_Arxiv2412_13833_monopole_green_time_reversal
-- name    : Arxiv2412_13833.monopole_green_time_reversal
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T12:56:24.019329+00:00
-- url     : https://prove2.me/theorems/19b116ef-c70f-40e7-8df6-06c89abeccac
-- title:
--   Eq. (A-10): $-G(-t)$ obeys (A-5) and $\mathcal L G_h=0$
-- statement:
--   Let $\rho(\mathbf x)>0$ and $c(\mathbf x)>0$ be smooth, time-independent coefficients of an inhomogeneous lossless medium in 2D or 3D. Fix $\mathbf x'$, and let $G$ be the causal monopole Green's function, $\mathcal LG=-\delta(\mathbf x-\mathbf x')\partial_t\delta(t)$. Let $G(\mathbf x,\mathbf x',-t)$ be its time reversal. Then:
--
--   1. $-G(\mathbf x,\mathbf x',-t)$ also obeys (A-5);
--   2. the homogeneous Green's function $G_h(\mathbf x,\mathbf x',t)=G(\mathbf x,\mathbf x',t)+G(\mathbf x,\mathbf x',-t)$ of (A-10) obeys
--
--   $$\mathcal LG_h=0.$$
--
--   **Formalization Note** The time reversal is given as a second distribution $G^R$ with $G^R(\varphi)=G(\varphi(\cdot,-\,\cdot))$, and $G_h$ is written $G+G^R$.
-- source:
--   Wapenaar, Multiple reflections on Huygens' principle, arXiv:2412.13833v2 (2025), claim c023; Appendix A-2, eqs. (A-5), (A-10), PDF p. 20

import Mathlib
import Definitions.Def_Arxiv2412_13833_Basic

open TopologicalSpace

namespace Arxiv2412_13833

theorem monopole_green_time_reversal {n : ℕ} (hn : n = 1 ∨ n = 2) (M : Medium n)
    (x' : Space n) (G GR : Distrib n)
    (hG : IsMonopoleGreen M x' G) (hR : IsTimeReversal G GR) :
    SolvesWave M (-GR) (monopoleSource x') ∧ SolvesWave M (G + GR) 0 := by sorry

end Arxiv2412_13833
