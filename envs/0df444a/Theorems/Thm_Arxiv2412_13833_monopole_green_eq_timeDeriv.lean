-- Prove2me | Theorems.Thm_Arxiv2412_13833_monopole_green_eq_timeDeriv
-- name    : Arxiv2412_13833.monopole_green_eq_timeDeriv
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T12:55:19.986536+00:00
-- url     : https://prove2.me/theorems/e7c14b81-c168-4b73-a426-6b677d836e22
-- title:
--   Eq. (A-6): the monopole Green's function is the time derivative of $\mathcal G$
-- statement:
--   Let $\rho(\mathbf x)>0$ and $c(\mathbf x)>0$ be smooth, time-independent coefficients of an inhomogeneous lossless medium in 2D or 3D, with $c$ bounded above. Fix a source point $\mathbf x'$. Let $\mathcal G$ be a causal distributional solution of
--
--   $$\mathcal L\mathcal G=-\delta(\mathbf x-\mathbf x')\delta(t),\qquad \mathcal L=\nabla\cdot\tfrac1\rho\nabla-\tfrac1{\rho c^2}\partial_t^2,$$
--
--   and let $G$ be a causal distributional solution of $\mathcal LG=-\delta(\mathbf x-\mathbf x')\partial_t\delta(t)$, the response to an impulsive volume-injection rate. Then
--
--   $$G(\mathbf x,\mathbf x',t)=\partial_t\mathcal G(\mathbf x,\mathbf x',t).$$
--
--   This relates the two monopole Green's functions used throughout the paper.
--
--   **Formalization Note** The paper's argument applies $\partial_t$ to (A-3) and then uses uniqueness of the causal solution of (A-5) without saying so. The hypothesis that $c$ is bounded above is added as a standard condition under which that uniqueness holds (finite propagation speed). Smoothness of $\rho$ and $c$ is needed for $\mathcal L$ to act on distributions.
-- source:
--   Wapenaar, Multiple reflections on Huygens' principle, arXiv:2412.13833v2 (2025), claim c021; Appendix A-1, eqs. (A-2)-(A-6), PDF p. 20

import Mathlib
import Definitions.Def_Arxiv2412_13833_Basic

open TopologicalSpace

namespace Arxiv2412_13833

theorem monopole_green_eq_timeDeriv {n : ℕ} (hn : n = 1 ∨ n = 2) (M : Medium n)
    (hc : ∃ C : ℝ, ∀ x, M.c x ≤ C) (x' : Space n) (Gc G : Distrib n)
    (hGc : IsImpulseGreen M x' Gc) (hG : IsMonopoleGreen M x' G) :
    G = timeDeriv Gc := by sorry

end Arxiv2412_13833
