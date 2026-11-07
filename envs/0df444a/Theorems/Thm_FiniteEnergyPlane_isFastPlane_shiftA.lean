-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isFastPlane_shiftA
-- name    : FiniteEnergyPlane.isFastPlane_shiftA
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T10:48:38.320958+00:00
-- url     : https://prove2.me/theorems/31d410f6-a931-4820-8742-160114f11f13
-- title:
--   Translations preserve fast finite-energy planes
-- statement:
--   Let $S = H^{-1}(1) \subset V_1 = \mathbb{R}^4$ be a strictly star-shaped level with a compatible complex structure $J$ on $\xi$. If $u : \mathbb{C} \to V_1 \setminus \{0\}$ is a fast finite-energy plane (Hryniewicz, Definition 2.14), then so is its translate $c \cdot u = e^{2c} u$ for every $c \in \mathbb{R}$.
--
--   This is used to transport statements about fast planes along translations in the $\mathbb{R}$-direction of the symplectization.
--
--   Formalization Note: `shiftA c u` is the map $z \mapsto e^{2c} \bullet u(z)$, which is how the translation $(a + c, w)$ of $\tilde u = (a, w)$ appears in the model $V_1 \setminus \{0\} \cong \mathbb{R} \times S$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Remark 3.10 and Definition 2.14

import Definitions.Def_FiniteEnergyPlane_Fredholm

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Fast finite-energy planes are invariant under translations in the `ℝ`-direction of the
symplectization: if `u` is a fast finite-energy plane (Hryniewicz, Definition 2.14), then so is
`c · u` for every `c : ℝ`. -/
theorem isFastPlane_shiftA (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (c : ℝ) : IsFastPlane H J (shiftA c u) := by
  sorry

end FiniteEnergyPlane
