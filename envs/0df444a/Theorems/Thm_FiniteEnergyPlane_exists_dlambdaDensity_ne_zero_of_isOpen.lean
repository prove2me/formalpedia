-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_dlambdaDensity_ne_zero_of_isOpen
-- name    : FiniteEnergyPlane.exists_dlambdaDensity_ne_zero_of_isOpen
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T10:20:15.177602+00:00
-- url     : https://prove2.me/theorems/bb256dc8-1aab-4cb3-9e63-dc19dabf1029
-- title:
--   The dλ-density of a nonconstant finite-energy plane vanishes on no open set
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level, $J$ a compatible complex structure on $\xi$, and $u$ a nonconstant finite-energy $\tilde J$-holomorphic plane, $w=\mathrm{proj}\circ u$. Then for every nonempty open set $U\subseteq\mathbb{C}$ there is $z\in U$ with $\omega_0(\partial_sw,\partial_tw)(z)\ne0$.
--
--   Equivalently, $\pi\,dw$ (the $\xi$-component of $dw$) does not vanish identically on any nonempty open subset of the plane; in particular not on any neighbourhood of $\infty$.
--
--   **Formalization Note** The density is `dlambdaDensity H u z`; nonconstant means $u(z_1)\ne u(z_2)$ for some $z_1,z_2$.
-- source:
--   Used for U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 2.11 (case of planes)

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- On a nonconstant finite-energy `J̃`-holomorphic plane, the `dλ`-density
`ω₀(∂ₛw, ∂ₜw)`, `w = proj ∘ u`, does not vanish identically on any nonempty open set. -/
theorem exists_dlambdaDensity_ne_zero_of_isOpen {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J Set.univ u)
    (hnc : ∃ z₁ z₂, u z₁ ≠ u z₂) (U : Set ℂ) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ z ∈ U, dlambdaDensity H u z ≠ 0 := by
  sorry

end FiniteEnergyPlane
