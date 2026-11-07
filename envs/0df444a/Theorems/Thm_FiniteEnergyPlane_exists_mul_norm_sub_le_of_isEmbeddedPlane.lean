-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_mul_norm_sub_le_of_isEmbeddedPlane
-- name    : FiniteEnergyPlane.exists_mul_norm_sub_le_of_isEmbeddedPlane
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T16:47:28.437613+00:00
-- url     : https://prove2.me/theorems/ea5a19d0-85b2-4c3c-9368-a3fb453623e2
-- title:
--   Global lower Lipschitz bound for an embedded fast plane in cylindrical scale
-- statement:
--   Let $u$ be an embedded fast finite-energy plane asymptotic to $P$ at $\infty$. Then there is $c > 0$ such that for all $z, z' \in \mathbb{C}$,
--   $$c \|z - z'\| \le (1 + \|z\| + \|z'\|) \big( |a(z) - a(z')| + \|w(z) - w(z')\| \big),$$
--   where $a = \mathtt{aCoord}\ H \circ u$ and $w = \mathtt{proj}\ H \circ u$.
--
--   **Role.** A quantitative form of embeddedness, uniform up to the end of the plane.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, used with Lemmas 6.10 and 6.20

import Definitions.Def_FiniteEnergyPlane_Fredholm

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- An embedded fast plane asymptotic to `P` at `∞` satisfies a global lower Lipschitz bound in its
symplectization coordinates, in the scale `1 + ‖z‖ + ‖z'‖`. -/
theorem exists_mul_norm_sub_le_of_isEmbeddedPlane (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : IsFastPlane H J u)
    (huP : IsNondegenerateEnd H u cylInf P 1) (hue : IsEmbeddedPlane u) :
    ∃ c > 0, ∀ z z' : ℂ, c * ‖z - z'‖ ≤ (1 + ‖z‖ + ‖z'‖) *
      (|aCoord H (u z) - aCoord H (u z')| + ‖proj H (u z) - proj H (u z')‖) := by
  sorry

end FiniteEnergyPlane
