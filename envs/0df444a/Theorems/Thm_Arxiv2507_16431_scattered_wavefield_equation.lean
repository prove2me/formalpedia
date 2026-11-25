-- Prove2me | Theorems.Thm_Arxiv2507_16431_scattered_wavefield_equation
-- name    : Arxiv2507_16431.scattered_wavefield_equation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T18:36:54.674038+00:00
-- url     : https://prove2.me/theorems/eaafd908-8f5b-53d7-b8d1-a8e23c763b52
-- title:
--   Eq. (2): the scattered wavefield solves the scattering form of the Helmholtz equation
-- statement:
--   Let $\Omega\subseteq\mathbb{R}^2$ be an open set of points $(x,z)$ and let $\omega>0$ be an angular frequency. Let $v$ be a velocity model and $v_0$ a reference (background) velocity model, both positive on $\Omega$. Let $f$ be a source term, and let $U$ and $U_0$ be complex-valued wavefields that are twice continuously differentiable on $\Omega$. Suppose that $U$ solves the Helmholtz equation (eq. 1) in the velocity $v$ and $U_0$ solves it in the background velocity $v_0$, with the same source:
--   $$\frac{\omega^2}{v^2}\,U+\nabla^2U=f,\qquad \frac{\omega^2}{v_0^2}\,U_0+\nabla^2U_0=f\qquad\text{on }\Omega.$$
--   Then the scattered wavefield $\delta U=U-U_0$ satisfies, at every point of $\Omega$,
--   $$\frac{\omega^2}{v^2}\,\delta U+\nabla^2\delta U+\omega^2\Big(\frac{1}{v^2}-\frac{1}{v_0^2}\Big)U_0=0.$$
--
--   This is the scattering form of the Helmholtz equation that the paper uses as the learning target of its neural operator, and whose residual, evaluated on the network output, is the physics loss $J_{\text{pde}}$ of eq. (8).
--
--   **Formalization Note** The paper does not write the operator $L$ of eq. (1), nor say that $U$ and $U_0$ are driven by the same source $f$; both are made explicit here, as they are what eq. (2) requires. The equations are taken in the classical pointwise sense on an arbitrary open set $\Omega$ on which both wavefields are $C^2$. The paper specifies no boundary conditions and none are used. For a point source the background wavefield of eq. (3) is singular at the source, and $\Omega$ can be taken to be the model domain with the source removed. The reference model $v_0$ is allowed to vary in space, as in the paper's statement of eq. (2); the constant background used afterwards is a special case.
-- source:
--   Ma and Alkhalifah, An effective physics-informed neural operator framework for predicting wavefields, arXiv:2507.16431v1 (2025), claim c015; Section 2.1 (Problem Statement), eqs. (1)-(2), PDF pp. 4-5

import Mathlib
import Definitions.Def_Arxiv2507_16431_Basic

namespace Arxiv2507_16431

theorem scattered_wavefield_equation (Ω : Set Plane) (hΩ : IsOpen Ω) (ω : ℝ) (hω : 0 < ω)
    (v v0 : Plane → ℝ) (hv : ∀ x ∈ Ω, 0 < v x) (hv0 : ∀ x ∈ Ω, 0 < v0 x)
    (f U U0 : Plane → ℂ) (hU : ContDiffOn ℝ 2 U Ω) (hU0 : ContDiffOn ℝ 2 U0 Ω)
    (hUeq : ∀ x ∈ Ω, helmholtzOp v ω U x = f x)
    (hU0eq : ∀ x ∈ Ω, helmholtzOp v0 ω U0 x = f x) :
    ∀ x ∈ Ω, ((ω ^ 2 / v x ^ 2 : ℝ) : ℂ) * scatteredField U U0 x
        + Laplacian.laplacian (scatteredField U U0) x
        + ((ω ^ 2 * (1 / v x ^ 2 - 1 / v0 x ^ 2) : ℝ) : ℂ) * U0 x = 0 := by sorry

end Arxiv2507_16431
