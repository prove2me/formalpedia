-- Prove2me | Theorems.Thm_Arxiv2412_13833_homogeneous_green_eq_timeDeriv
-- name    : Arxiv2412_13833.homogeneous_green_eq_timeDeriv
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T12:57:20.144225+00:00
-- url     : https://prove2.me/theorems/7517e0d5-af63-5bb5-80fe-c3d95af7bdbd
-- title:
--   Eq. (A-11): $G_h=\partial_t\mathcal G_h$
-- statement:
--   Let $\rho(\mathbf x)>0$ and $c(\mathbf x)>0$ be smooth, time-independent coefficients of an inhomogeneous lossless medium in 2D or 3D, with $c$ bounded above. Fix $\mathbf x'$. Let $\mathcal G$ be the causal solution of (A-3) and $G$ the causal solution of (A-5). With the homogeneous Green's functions
--
--   $$\mathcal G_h(\mathbf x,\mathbf x',t)=\mathcal G(\mathbf x,\mathbf x',t)-\mathcal G(\mathbf x,\mathbf x',-t),\qquad G_h(\mathbf x,\mathbf x',t)=G(\mathbf x,\mathbf x',t)+G(\mathbf x,\mathbf x',-t)$$
--
--   of (A-9) and (A-10), one has
--
--   $$G_h(\mathbf x,\mathbf x',t)=\partial_t\mathcal G_h(\mathbf x,\mathbf x',t).$$
--
--   **Formalization Note** The time reversals are given as distributions $\mathcal G^R$ and $G^R$ characterized by their action on test functions. The relation (A-6), $G=\partial_t\mathcal G$, on which the paper's derivation rests, is not assumed: it follows from the hypotheses, as in the statement for (A-6), which is why $c$ is again assumed bounded above.
-- source:
--   Wapenaar, Multiple reflections on Huygens' principle, arXiv:2412.13833v2 (2025), claim c024; Appendix A-2, eqs. (A-6), (A-9)-(A-11), PDF p. 20

import Mathlib
import Definitions.Def_Arxiv2412_13833_Basic

open TopologicalSpace

namespace Arxiv2412_13833

theorem homogeneous_green_eq_timeDeriv {n : ℕ} (hn : n = 1 ∨ n = 2) (M : Medium n)
    (hc : ∃ C : ℝ, ∀ x, M.c x ≤ C) (x' : Space n) (Gc GcR G GR : Distrib n)
    (hGc : IsImpulseGreen M x' Gc) (hG : IsMonopoleGreen M x' G)
    (hGcR : IsTimeReversal Gc GcR) (hGR : IsTimeReversal G GR) :
    G + GR = timeDeriv (Gc - GcR) := by sorry

end Arxiv2412_13833
