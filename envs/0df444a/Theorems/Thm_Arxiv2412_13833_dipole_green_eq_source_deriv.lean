-- Prove2me | Theorems.Thm_Arxiv2412_13833_dipole_green_eq_source_deriv
-- name    : Arxiv2412_13833.dipole_green_eq_source_deriv
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T12:56:54.912492+00:00
-- url     : https://prove2.me/theorems/7f743c3c-324e-4497-acfc-9c9549a10364
-- title:
--   Eq. (A-14): $G_d=\frac{1}{\rho(\mathbf x')}\partial_{z'}\mathcal G$
-- statement:
--   Let $\rho(\mathbf x)>0$ and $c(\mathbf x)>0$ be smooth, time-independent coefficients of an inhomogeneous lossless medium in 2D or 3D, with $c$ bounded above. For every source point $\mathbf y$, let $\mathcal G(\cdot,\mathbf y,\cdot)$ be the causal solution of $\mathcal L\mathcal G=-\delta(\mathbf x-\mathbf y)\delta(t)$. Fix $\mathbf x'=(\mathbf x_H',z')$ and let $G_d$ be the causal dipole Green's function,
--
--   $$\mathcal LG_d=\frac{1}{\rho(\mathbf x')}\partial_z\delta(\mathbf x-\mathbf x')\delta(t).$$
--
--   Then $\mathcal G$ is differentiable in the depth $z'$ of the source point when tested against each fixed test function, and
--
--   $$G_d(\mathbf x,\mathbf x',t)=\frac{1}{\rho(\mathbf x')}\,\partial_{z'}\mathcal G(\mathbf x,\mathbf x',t).$$
--
--   That is, for every test function $\varphi$ the map $s\mapsto\mathcal G(\cdot,\mathbf x'+s\mathbf e_z,\cdot)(\varphi)$ is differentiable at $s=0$ with derivative $\rho(\mathbf x')\,G_d(\varphi)$.
--
--   **Formalization Note** The equation is stated in the equivalent form $\partial_{z'}\mathcal G=\rho(\mathbf x')G_d$, using $\rho>0$. The paper differentiates (A-3) with respect to $z'$ without showing that the derivative exists, so the formal statement asserts its existence. The argument also uses uniqueness of the causal solution of (A-12), hence the bound on $c$.
-- source:
--   Wapenaar, Multiple reflections on Huygens' principle, arXiv:2412.13833v2 (2025), claim c025; Appendix A-3, eqs. (A-12)-(A-14), PDF pp. 20-21

import Mathlib
import Definitions.Def_Arxiv2412_13833_Basic

open TopologicalSpace

namespace Arxiv2412_13833

theorem dipole_green_eq_source_deriv {n : ℕ} (hn : n = 1 ∨ n = 2) (M : Medium n)
    (hc : ∃ C : ℝ, ∀ x, M.c x ≤ C) (Gc : Space n → Distrib n)
    (hGc : ∀ y, IsImpulseGreen M y (Gc y)) (x' : Space n) (Gd : Distrib n)
    (hGd : IsDipoleGreen M x' Gd) :
    ∀ φ : TestFn n,
      HasDerivAt (fun s : ℝ => Gc (x' + s • zSpaceDir) φ) (M.rho x' * Gd φ) 0 := by sorry

end Arxiv2412_13833
