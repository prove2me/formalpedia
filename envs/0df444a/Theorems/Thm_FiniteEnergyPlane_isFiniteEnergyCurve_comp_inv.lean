-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isFiniteEnergyCurve_comp_inv
-- name    : FiniteEnergyPlane.isFiniteEnergyCurve_comp_inv
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T10:42:55.128562+00:00
-- url     : https://prove2.me/theorems/2668fb71-5898-472f-a2cd-f8fd4e9d741e
-- title:
--   A finite-energy plane in the coordinate at infinity
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level, $J$ a compatible complex structure on $\xi$, and $u:\mathbb{C}\to\mathbb{R}^{2n+2}\setminus\{0\}$ a finite-energy $\tilde J$-holomorphic plane. Then $\tilde u(z)=u(z^{-1})$ is a finite-energy $\tilde J$-holomorphic curve on the punctured disc $D\setminus\{0\}$, and for $z\ne0$ its $d\lambda$-density satisfies $$\omega_0(\partial_s\tilde w,\partial_t\tilde w)(z)=|z|^{-4}\,\omega_0(\partial_sw,\partial_tw)(z^{-1}),\qquad w=\mathrm{proj}\circ u,\ \tilde w=\mathrm{proj}\circ\tilde u.$$
--
--   So the puncture at $\infty$ of a plane can be treated as the puncture $0$ of a curve on $D\setminus\{0\}$.
--
--   **Formalization Note** Finite-energy curves are `IsFiniteEnergyCurve` (smooth, avoiding $0$, $\tilde J$-holomorphic, Hofer energy $<\infty$); the density is `dlambdaDensity`.
-- source:
--   Used for U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 2.11 (case of planes)

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A finite-energy `J̃`-holomorphic plane `u`, read in the coordinate `z ↦ z⁻¹` at `∞`, is a
finite-energy `J̃`-holomorphic curve on the punctured unit disc, and its `dλ`-density there is
`|z|⁻⁴` times the density of `u` at `z⁻¹`. -/
theorem isFiniteEnergyCurve_comp_inv {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J Set.univ u) :
    IsFiniteEnergyCurve H J (ball 0 1 \ {0}) (fun z => u z⁻¹) ∧
      ∀ z : ℂ, z ≠ 0 →
        dlambdaDensity H (fun z => u z⁻¹) z = (‖z‖ ^ 4)⁻¹ * dlambdaDensity H u z⁻¹ := by
  sorry

end FiniteEnergyPlane
