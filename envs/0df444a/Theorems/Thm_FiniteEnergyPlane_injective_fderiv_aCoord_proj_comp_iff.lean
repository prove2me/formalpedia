-- Prove2me | Theorems.Thm_FiniteEnergyPlane_injective_fderiv_aCoord_proj_comp_iff
-- name    : FiniteEnergyPlane.injective_fderiv_aCoord_proj_comp_iff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T16:43:26.931492+00:00
-- url     : https://prove2.me/theorems/e4a263f4-d68c-4914-a017-478435e43645
-- title:
--   Immersions in the symplectization coordinates
-- statement:
--   Let $S = H^{-1}(1)$ be a strictly star-shaped level, and let $u : E \to \mathbb{R}^{2n+2}$ be differentiable at $z$ with $u(z) \ne 0$. Then the derivative at $z$ of $w \mapsto (\mathtt{aCoord}\ H (u(w)), \mathtt{proj}\ H (u(w)))$ is injective if and only if $Du(z)$ is injective.
--
--   **Role.** Immersions may be tested in either the linear or the symplectization coordinates.
-- source:
--   Elementary lemma in the setting of U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- If `u : E → V n` is differentiable at `z`, `u z ≠ 0`, then the derivative of `u` at `z` is
injective if and only if the derivative at `z` of the symplectization coordinates
`w ↦ (aCoord H (u w), proj H (u w))` is. -/
theorem injective_fderiv_aCoord_proj_comp_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (u : E → V n) (z : E)
    (hu : DifferentiableAt ℝ u z) (h0 : u z ≠ 0) :
    Function.Injective (fderiv ℝ (fun w => (aCoord H (u w), proj H (u w))) z) ↔
      Function.Injective (fderiv ℝ u z) := by
  sorry

end FiniteEnergyPlane
