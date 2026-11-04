-- Prove2me | Theorems.Thm_FiniteEnergyPlane_norm_dbar_xiPart_le_on
-- name    : FiniteEnergyPlane.norm_dbar_xiPart_le_on
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-02T20:57:12.857354+00:00
-- url     : https://prove2.me/theorems/12fe52c1-eef8-49f6-b103-d349db06b208
-- title:
--   Local linear Cauchy–Riemann inequality for the $\xi$-part of $\partial_s(\mathrm{pr}\circ u)$ on an open set
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $\tilde J$ the induced almost complex structure on $\mathbb{R}^{2n+2}\setminus\{0\}$. Let $U\subseteq\mathbb{C}$ be open and $u:U\to\mathbb{R}^{2n+2}\setminus\{0\}$ a smooth $\tilde J$-holomorphic map, $w=\mathrm{pr}\circ u$, and
--   $$\zeta(z)=\pi_{w(z)}\,\partial_s w(z),\qquad \pi_w v=v-\frac{dH(w)v}{dH(w)w}\,w-\lambda_0(w)(v)\,R(w).$$
--   Then every $z_0\in U$ has a disc $B(z_0,\rho)\subseteq U$ and a constant $M$ with
--   $$\big\|\partial_s\zeta+\tilde J(u)\,\partial_t\zeta\big\|\le M\,\|\zeta\|\quad\text{on }B(z_0,\rho).$$
--
--   This is the version of `norm_dbar_xiPart_le` (89044077) for maps defined only on an open subset of $\mathbb{C}$, as needed near the punctures of a finite-energy sphere.
--
--   **Formalization Note** The map is given by `ContDiffOn ℝ ∞ u U`, `u z ≠ 0` on `U` and `JHolomorphic.IsJHolomorphicOn (Jtilde H J) U u`; $\zeta$ is written out with `proj`, `liouville` and `reeb` exactly as in `norm_dbar_xiPart_le`.
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2.4 (local version of the inequality behind formula (14))

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- For a smooth `J̃`-holomorphic map `u ≠ 0` on an open set
`U ⊆ ℂ`, the `ξ`-part `ζ = π_w ∂ₛw` of `w = proj ∘ u` satisfies a linear Cauchy–Riemann inequality
with respect to `J̃(u)` on a disc around each point of `U`. -/
theorem norm_dbar_xiPart_le_on {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → V n) (hu : ContDiffOn ℝ ∞ u U) (hu0 : ∀ z ∈ U, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) U u) (z₀ : ℂ) (hz₀ : z₀ ∈ U) :
    let ζ : ℂ → V n := fun z =>
      let w := proj H (u z)
      let v := fderiv ℝ (fun z => proj H (u z)) z 1
      v - (fderiv ℝ H w v / fderiv ℝ H w w) • w - liouville w v • reeb H w
    ∃ ρ > (0 : ℝ), ball z₀ ρ ⊆ U ∧ ∃ M : ℝ, ∀ z ∈ ball z₀ ρ,
      ‖fderiv ℝ ζ z 1 + Jtilde H J (u z) (fderiv ℝ ζ z Complex.I)‖ ≤ M * ‖ζ z‖ := by
  sorry

end FiniteEnergyPlane
