-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_unitaryXiFrame_hasXiLoopWind_iff
-- name    : FiniteEnergyPlane.exists_unitaryXiFrame_hasXiLoopWind_iff
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-01T15:37:33.65458+00:00
-- url     : https://prove2.me/theorems/ccbe5d28-69bb-40b9-afe0-38bdace12be1
-- title:
--   A unitary frame along a Reeb orbit homotopic to the global frame
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. For every periodic Reeb orbit $P=(x,T)$ there is a unitary frame $Z$ of $\xi$ along $P$ such that for every continuous $1$-periodic nowhere-vanishing $\zeta:\mathbb{R}\to\mathbb{R}^2$ and every $k\in\mathbb{Z}$: the loop $t\mapsto Z(t)\zeta(t)$ has winding $k$ in the global frame if and only if $\zeta$ has winding $k$ as a loop in $\mathbb{C}$.
--
--   **Formalization Note** Unitary frames are `IsUnitaryXiFrame J P Z` of `FiniteEnergyPlane_Asymptotics`; $\mathbb{R}^2\to\mathbb{C}$ is $(q,p)\mapsto q+ip$ (`vecToC`).
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Remark 2.6 and Remark 2.13

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz, Remark 2.6, for `n = 1`: along every periodic Reeb orbit `P` there is a unitary
frame `Z` of `ξ` that is homotopic to the global frame `Z₁, Z₂`, in the sense that a loop
`t ↦ Z(t) ζ(t)` has the same winding number in the global frame as `ζ` has in `ℝ² = ℂ`. -/
theorem exists_unitaryXiFrame_hasXiLoopWind_iff (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H) :
    ∃ Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1, IsUnitaryXiFrame J P Z ∧
      ∀ ζ : ℝ → CauchyRiemannIndex.Vec 1, Continuous ζ → Function.Periodic ζ 1 →
        (∀ t : ℝ, ζ t ≠ 0) → ∀ k : ℤ,
          (HasXiLoopWind P (fun t => Z t (ζ t)) k ↔ HasLoopWind (fun t => vecToC (ζ t)) k) := by
  sorry

end FiniteEnergyPlane
