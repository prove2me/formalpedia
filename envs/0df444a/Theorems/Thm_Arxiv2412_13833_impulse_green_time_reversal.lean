-- Prove2me | Theorems.Thm_Arxiv2412_13833_impulse_green_time_reversal
-- name    : Arxiv2412_13833.impulse_green_time_reversal
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T12:55:47.09166+00:00
-- url     : https://prove2.me/theorems/d6a1358e-e5a6-52a9-a73f-b455a9f2b41b
-- title:
--   Eq. (A-9): $\mathcal G(-t)$ obeys (A-3) and $\mathcal L\mathcal G_h=0$
-- statement:
--   Let $\rho(\mathbf x)>0$ and $c(\mathbf x)>0$ be smooth, time-independent coefficients of an inhomogeneous lossless medium in 2D or 3D. Fix $\mathbf x'$, and let $\mathcal G$ be the causal Green's function, $\mathcal L\mathcal G=-\delta(\mathbf x-\mathbf x')\delta(t)$. Let $\mathcal G(\mathbf x,\mathbf x',-t)$ be its time reversal. Then:
--
--   1. the time-reversed Green's function also obeys (A-3), $\mathcal L\,\mathcal G(\mathbf x,\mathbf x',-t)=-\delta(\mathbf x-\mathbf x')\delta(t)$;
--   2. the homogeneous Green's function $\mathcal G_h(\mathbf x,\mathbf x',t)=\mathcal G(\mathbf x,\mathbf x',t)-\mathcal G(\mathbf x,\mathbf x',-t)$ of (A-9) obeys the source-free equation
--
--   $$\mathcal L\mathcal G_h=0.$$
--
--   **Formalization Note** The time reversal is given as a second distribution $\mathcal G^R$ with $\mathcal G^R(\varphi)=\mathcal G(\varphi(\cdot,-\,\cdot))$ for every test function $\varphi$, and $\mathcal G_h$ is written $\mathcal G-\mathcal G^R$.
-- source:
--   Wapenaar, Multiple reflections on Huygens' principle, arXiv:2412.13833v2 (2025), claim c022; Appendix A-2, eqs. (A-3), (A-9), PDF p. 20

import Mathlib
import Definitions.Def_Arxiv2412_13833_Basic

open TopologicalSpace

namespace Arxiv2412_13833

theorem impulse_green_time_reversal {n : ℕ} (hn : n = 1 ∨ n = 2) (M : Medium n)
    (x' : Space n) (Gc GcR : Distrib n)
    (hGc : IsImpulseGreen M x' Gc) (hR : IsTimeReversal Gc GcR) :
    SolvesWave M GcR (impulseSource x') ∧ SolvesWave M (Gc - GcR) 0 := by sorry

end Arxiv2412_13833
