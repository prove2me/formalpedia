-- Prove2me | Theorems.Thm_FiniteEnergyPlane_fderiv_tubeMap_apply_zero
-- name    : FiniteEnergyPlane.fderiv_tubeMap_apply_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-16T10:58:57.439066+00:00
-- url     : https://prove2.me/theorems/2e5f50cd-be26-48ab-95bd-3bccd76b8d45
-- title:
--   The derivative of the tube map u(z) + N(z)w along the zero section
-- statement:
--   Let $F$ be a real normed space, $u:\mathbb C\to F$ differentiable and $N:\mathbb C\to L_{\mathbb R}(\mathbb C,F)$ differentiable. For the map
--   $$\Phi(z,w)=u(z)+N(z)\,w,\qquad (z,w)\in\mathbb C\times\mathbb C,$$
--   the derivative along the zero section $w=0$ is
--   $$D\Phi(z,0)(\Delta,\nu)=Du(z)\,\Delta+N(z)\,\nu\qquad(z,\Delta,\nu\in\mathbb C).$$
--
--   This computes the linearization of a tube map built from a curve $u$ and a family of normal maps $N$ along the curve itself.
--
--   Formalization Note: derivatives are `fderiv ℝ`; $\mathbb C$ is a real normed space.
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6

import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Complex.Basic

namespace FiniteEnergyPlane

/-- The derivative of the map `Φ(z, w) = u z + N z w` along the zero section: for differentiable
`u : ℂ → F` and `N : ℂ → (ℂ →L[ℝ] F)`, `DΦ(z, 0)(Δ, ν) = Du(z) Δ + N z ν`. -/
theorem fderiv_tubeMap_apply_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : ℂ → F) (N : ℂ → ℂ →L[ℝ] F) (hu : Differentiable ℝ u) (hN : Differentiable ℝ N)
    (z Δ ν : ℂ) :
    fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) (z, 0) (Δ, ν) = fderiv ℝ u z Δ + N z ν := by
  sorry

end FiniteEnergyPlane
