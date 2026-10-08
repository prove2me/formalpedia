-- Prove2me | Theorems.Thm_CatalyticRD_crd2_integral_laplacian_neumann
-- name    : CatalyticRD.crd2_integral_laplacian_neumann
-- status  : Open
-- author  : @shivm
-- created : 2026-10-04T18:27:29.260898+00:00
-- url     : https://prove2.me/theorems/57319d0a-ef65-4c12-a6f2-be3ea03f3bb6
-- title:
--   Neumann functions have $\int_\Omega \Delta u = 0$
-- statement:
--   Let $\Omega=\{\varphi<0\}\subset\mathbb R^n$ be a smooth bounded domain (as in `CatalyticRD_Setup`). If $u\in C^2(\overline\Omega)$ and $\partial_\nu u=0$ on $\partial\Omega$, then
--
--   $$\int_\Omega \Delta u\,dx=0.$$
--
--   This is the divergence theorem $\int_\Omega\Delta u=\int_{\partial\Omega}\partial_\nu u\,dS$. It gives conservation of mass for Neumann reaction–diffusion systems.
--
--   **Formalization Note** The normal derivative at $x\in\partial\Omega$ is $Du(x)[\nabla\varphi(x)]$, with $Du$ taken within $\overline\Omega$. $\Delta u$ is the full-space Laplacian; on the open set $\Omega$ it agrees with the one computed within $\overline\Omega$.
-- source:
--   Divergence (Gauss–Green) theorem applied to the vector field $\nabla u$: L. C. Evans, Partial Differential Equations, 2nd ed., AMS GSM 19 (2010), Appendix C.2, Theorem 1 and Theorem 3 (Green's formula (i): $\int_U \Delta u\,dx=\int_{\partial U}\partial u/\partial\nu\,dS$).

import Mathlib
import Definitions.Def_CatalyticRD_Setup

open MeasureTheory Set Filter Topology Laplacian

namespace CatalyticRD

theorem crd2_integral_laplacian_neumann {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hΩ : IsSmoothBoundedDomain Ω φ)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (hu : ContDiffOn ℝ 2 u (closure Ω))
    (hN : NeumannBC Ω φ u) : ∫ x in Ω, Δ u x = 0 := by sorry

end CatalyticRD
