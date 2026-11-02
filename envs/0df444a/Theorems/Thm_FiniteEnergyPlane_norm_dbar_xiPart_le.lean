-- Prove2me | Theorems.Thm_FiniteEnergyPlane_norm_dbar_xiPart_le
-- name    : FiniteEnergyPlane.norm_dbar_xiPart_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T11:30:14.262836+00:00
-- url     : https://prove2.me/theorems/89044077-edfe-427e-9839-243f22719848
-- title:
--   A Cauchy–Riemann inequality for the contact part of a pseudoholomorphic plane
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level with Liouville form $\lambda_0$, Reeb field $R$ and contact structure $\xi=\ker\lambda_0\cap TS$, let $J$ be a $d\lambda_0$-compatible complex structure on $\xi$, and $\tilde J$ the induced almost complex structure on $\mathbb{R}^{2n+2}\setminus\{0\}\cong\mathbb{R}\times S$. Let $u:\mathbb{C}\to\mathbb{R}^{2n+2}\setminus\{0\}$ be smooth and $\tilde J$-holomorphic, and $w=\mathrm{proj}\circ u:\mathbb{C}\to S$. For $x\in S$ let $\pi_x v=v-\frac{dH(x)v}{dH(x)x}\,x-\lambda_0(x)(v)\,R(x)$, and put $\zeta(z)=\pi_{w(z)}\,\partial_s w(z)$. Then every $z_0\in\mathbb{C}$ has a disc $B(z_0,\rho)$, $\rho>0$, and a constant $M$ with $$\|\partial_s\zeta(z)+\tilde J(u(z))\,\partial_t\zeta(z)\|\le M\,\|\zeta(z)\|\qquad(z\in B(z_0,\rho)).$$
--
--   The section $\zeta$ is the $\xi$-component of the derivative of the projected curve; this inequality makes it amenable to unique continuation and to the study of its zeros.
--
--   **Formalization Note** $\partial_s f(z)=$ `fderiv ℝ f z 1`, $\partial_t f(z)=$ `fderiv ℝ f z Complex.I`; `proj`, `reeb`, `liouville` and `Jtilde` are from the shared setting file. $J$-holomorphicity is `IsJHolomorphicOn (Jtilde H J) Set.univ u`.
-- source:
--   Used for U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 2.11 (case of planes)

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `u : ℂ → V n \ {0}` be a smooth `J̃`-holomorphic map and `w = proj ∘ u`. With
`π_w v = v - (dH(w) v / dH(w) w) w - λ₀(w)(v) R(w)`, the `ξ`-part `ζ = π_w ∂ₛw` satisfies near every
point a linear Cauchy–Riemann inequality `‖∂ₛζ + J̃(u) ∂ₜζ‖ ≤ M ‖ζ‖`. -/
theorem norm_dbar_xiPart_le {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : ContDiff ℝ ∞ u) (hu0 : ∀ z, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) Set.univ u) (z₀ : ℂ) :
    let ζ : ℂ → V n := fun z =>
      let w := proj H (u z)
      let v := fderiv ℝ (fun z => proj H (u z)) z 1
      v - (fderiv ℝ H w v / fderiv ℝ H w w) • w - liouville w v • reeb H w
    ∃ ρ > (0 : ℝ), ∃ M : ℝ, ∀ z ∈ ball z₀ ρ,
      ‖fderiv ℝ ζ z 1 + Jtilde H J (u z) (fderiv ℝ ζ z Complex.I)‖ ≤ M * ‖ζ z‖ := by
  sorry

end FiniteEnergyPlane
