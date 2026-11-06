-- Prove2me | Theorems.Thm_FiniteEnergyPlane_differentiableAt_complex_of_eventuallyEq_comp
-- name    : FiniteEnergyPlane.differentiableAt_complex_of_eventuallyEq_comp
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-05T20:54:05.348005+00:00
-- url     : https://prove2.me/theorems/5f7b3c3b-720e-4869-9db5-a38b9e3efd57
-- title:
--   A real differentiable reparametrization between $J$-holomorphic maps is complex differentiable
-- statement:
--   Let $E$ be a real normed space, $J:E\to\mathrm{End}_{\mathbb{R}}(E)$, $u,v:\mathbb{C}\to E$ and $\varphi:\mathbb{C}\to\mathbb{C}$ with $u=v\circ\varphi$ near $z$. Suppose $\varphi$ is real differentiable at $z$, $v$ is real differentiable at $\varphi(z)$ with injective derivative, $J(u(z))^2=-1$, and the equation $\partial_s+J\partial_t=0$ holds for $u$ at $z$ and for $v$ at $\varphi(z)$. Then $\varphi$ is complex differentiable at $z$.
--
--   Role: pointwise statement identifying reparametrizations between curves as holomorphic, needing no regularity beyond one derivative at the point.
-- source:
--   Standard fact on pseudoholomorphic maps, cf. D. McDuff, D. Salamon, J-holomorphic Curves and Symplectic Topology, Chapter 2

import Definitions.Def_JHolomorphic_Setting

namespace FiniteEnergyPlane

open Filter Topology

/-- Let `u = v ∘ φ` near `z`, with `φ : ℂ → ℂ` real differentiable at `z`, `v` real differentiable at
`φ z` with injective derivative, and suppose `J(u z)² = -1` and the Cauchy-Riemann equation
`∂ₛ + J ∂ₜ = 0` holds for `u` at `z` and for `v` at `φ z`. Then `φ` is complex differentiable at
`z`. -/
theorem differentiableAt_complex_of_eventuallyEq_comp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (J : E → E →L[ℝ] E) (u v : ℂ → E) (φ : ℂ → ℂ) (z : ℂ)
    (hJ2 : (J (u z)).comp (J (u z)) = -ContinuousLinearMap.id ℝ E)
    (hφ : DifferentiableAt ℝ φ z) (hv : DifferentiableAt ℝ v (φ z))
    (heq : u =ᶠ[𝓝 z] v ∘ φ)
    (huh : fderiv ℝ u z 1 + J (u z) (fderiv ℝ u z Complex.I) = 0)
    (hvh : fderiv ℝ v (φ z) 1 + J (v (φ z)) (fderiv ℝ v (φ z) Complex.I) = 0)
    (hvi : Function.Injective (fderiv ℝ v (φ z))) :
    DifferentiableAt ℂ φ z := by
  sorry

end FiniteEnergyPlane
