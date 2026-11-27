-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isFiniteEnergyCurve_orbitCylinder
-- name    : FiniteEnergyPlane.isFiniteEnergyCurve_orbitCylinder
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-26T22:19:14.775959+00:00
-- url     : https://prove2.me/theorems/c76e5b44-7f15-524d-b7b9-c9eab6556306
-- title:
--   The trivial cylinder over a periodic Reeb orbit in logarithmic coordinates
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$ be a strictly star-shaped level, $J$ any map into the endomorphisms of $\mathbb{R}^4$ and $\tilde J$ the associated almost complex structure on the symplectization $\mathbb{R}\times S \cong \mathbb{R}^4\setminus\{0\}$. Let $P = (x, T)$ be a periodic Reeb orbit. Then the map $v(\zeta) = e^{2\operatorname{Re}\zeta}\, x(\operatorname{Im}\zeta)$ (the point with $\mathbb{R}$-coordinate $\operatorname{Re}\zeta$ over $x(\operatorname{Im}\zeta)$) is, on every ball $B_r(w_0)\subset\mathbb{C}$, a finite-energy $\tilde J$-holomorphic curve; its derivative is injective at every point of $\mathbb{C}$; and its projection to $S$ is $\zeta\mapsto x(\operatorname{Im}\zeta)$.
--
--   Role: a smooth immersed parametrization of the trivial cylinder $\mathbb{R}\times x(\mathbb{R})$ to which the intersection theory of pseudoholomorphic immersions (persistence of isolated intersections, holomorphic reparametrization at non-isolated ones) can be applied.
-- source:
--   Standard fact in the setting of H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II (1995), § 4, and U. Hryniewicz, J. Symplectic Geom. 12 (2014), § 3

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open Metric
open scoped ContDiff

/-- The trivial cylinder `ℝ × x(ℝ)` over a periodic Reeb orbit `P = (x, T)` in logarithmic coordinates: the map
`ζ ↦ e^{2 Re ζ} x(Im ζ)` (the point of `ℝ × S` with `a = Re ζ` over `x(Im ζ)`) is, on every ball, a finite-energy
`J̃`-holomorphic curve; its derivative is injective at every point; and its projection to `S` is
`ζ ↦ x(Im ζ)`. -/
theorem isFiniteEnergyCurve_orbitCylinder (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H) (w₀ : ℂ) (r : ℝ) :
    IsFiniteEnergyCurve H J (ball w₀ r) (fun ζ : ℂ => Real.exp (2 * ζ.re) • P.x ζ.im) ∧
      (∀ ζ : ℂ, Function.Injective (fderiv ℝ (fun ζ : ℂ => Real.exp (2 * ζ.re) • P.x ζ.im) ζ)) ∧
      ∀ ζ : ℂ, proj H (Real.exp (2 * ζ.re) • P.x ζ.im) = P.x ζ.im := by
  sorry

end FiniteEnergyPlane
