-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isCompact_aCoord_slab
-- name    : FiniteEnergyPlane.isCompact_aCoord_slab
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-25T18:17:59.588134+00:00
-- url     : https://prove2.me/theorems/360f6763-c929-45bb-9bb9-435ab7b62094
-- title:
--   Slabs of the symplectization of a star-shaped level are compact
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^{2n+2}$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Identify $\mathbb R^{2n+2}\setminus\{0\}$ with $\mathbb R\times S$ by $y=e^{2a}x$, $x\in S$. Then for every $A\in\mathbb R$ the slab
--   $$\{\,y\in\mathbb R^{2n+2}\setminus\{0\}\ :\ |a(y)|\le A\,\}$$
--   is compact.
--
--   Slabs are the compact subsets of the symplectization in which curves with bounded $\mathbb R$-coordinate take their values.
--
--   **Formalization Note** $a(y)$ is `aCoord H y`. The compatible structure $J$ does not enter the conclusion.
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, p. 12; H. Hofer, Invent. Math. 114 (1993), Section 3; C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Prop. 9.1

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Slabs of the symplectization are compact. For a strictly star-shaped level `S = H⁻¹(1)` and
`A ∈ ℝ`, the set `{y ≠ 0 : |a(y)| ≤ A} ≅ [-A, A] × S` is a compact subset of `ℝ^{2n+2}`. -/
theorem isCompact_aCoord_slab {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (A : ℝ) :
    IsCompact {y : V n | y ≠ 0 ∧ |aCoord H y| ≤ A} := by
  sorry

end FiniteEnergyPlane
