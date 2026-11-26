-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasDerivAt_wedge_flow
-- name    : FiniteEnergyPlane.hasDerivAt_wedge_flow
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-26T21:20:55.149912+00:00
-- url     : https://prove2.me/theorems/fd3fade7-40c8-53b2-8ebc-06dde5791591
-- title:
--   Transport of the area form along a planar flow
-- statement:
--   Let $X$ be a smooth vector field on $\mathbb{C} = \mathbb{R}^2$ and let $\psi$ be a jointly smooth flow of $X$, i.e. $\partial_s \psi_s(y) = X(\psi_s(y))$. Write $\omega(a,b) = \operatorname{Re} a \operatorname{Im} b - \operatorname{Im} a \operatorname{Re} b$ for the standard area form and $\operatorname{div} X = \operatorname{Re}(DX\cdot 1) + \operatorname{Im}(DX \cdot i)$.
--
--   For every point $y$ and vector $w$, the function $s \mapsto \omega\big(X(\psi_s y),\, D\psi_s(y)\, w\big)$ is differentiable, with derivative $(\operatorname{div} X)(\psi_s y)\cdot \omega\big(X(\psi_s y), D\psi_s(y) w\big)$.
--
--   Role: this is the evolution law of the Jacobian of a sweep $(s,t) \mapsto \psi_s(c(t))$ of a curve by a planar flow; it is reusable for any area computation along flows in the plane.
-- source:
--   Elementary lemma in the setting of U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), § 3.2

import Mathlib

namespace FiniteEnergyPlane

open scoped ContDiff

/-- Transport of the area form along a flow in the plane. Let `ψ` be a jointly smooth flow of a smooth
autonomous vector field `X` on `ℂ = ℝ²`. For a point `y` and a vector `w`, the area
`ω(X(ψ_s y), Dψ_s(y) w)`, with `ω(a, b) = a.re b.im - a.im b.re`, is differentiable in `s`, and its
derivative is the divergence `div X = (DX · 1).re + (DX · i).im` at `ψ_s y` times the area itself. -/
theorem hasDerivAt_wedge_flow (X : ℂ → ℂ) (hX : ContDiff ℝ ∞ X) (ψ : ℝ → ℂ → ℂ)
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × ℂ => ψ p.1 p.2))
    (hflow : ∀ t y, HasDerivAt (fun s => ψ s y) (X (ψ t y)) t) (t : ℝ) (y w : ℂ) :
    HasDerivAt (fun s => (X (ψ s y)).re * (fderiv ℝ (ψ s) y w).im -
        (X (ψ s y)).im * (fderiv ℝ (ψ s) y w).re)
      (((fderiv ℝ X (ψ t y) 1).re + (fderiv ℝ X (ψ t y) Complex.I).im) *
        ((X (ψ t y)).re * (fderiv ℝ (ψ t) y w).im - (X (ψ t y)).im * (fderiv ℝ (ψ t) y w).re)) t := by
  sorry

end FiniteEnergyPlane
