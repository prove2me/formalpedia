-- Prove2me | Theorems.Thm_FiniteEnergyPlane_contDiffOn_pageMap
-- name    : FiniteEnergyPlane.contDiffOn_pageMap
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-22T19:33:33.175928+00:00
-- url     : https://prove2.me/theorems/c25cc8e5-8874-4afa-8215-5e2cee79c393
-- title:
--   The projection of a nonvanishing C^1 family to S is C^1
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be strictly star-shaped, $I\subseteq\mathbb{R}$ open, and $U:\mathbb{R}\times\mathbb{C}\to\mathbb{R}^4$ of class $C^1$ on $I\times\mathbb{C}$ with $U(p)\neq0$ for $p\in I\times\mathbb{C}$. Then $\mathrm{pr}_S\circ U$ is of class $C^1$ on $I\times\mathbb{C}$, where $\mathrm{pr}_S:\mathbb{R}^4\setminus\{0\}\to S$ is the radial projection.
--
--   It provides the regularity of the projected family $(t,z)\mapsto\mathrm{pr}_S U(t,z)$ used for families of planes along a Reeb trajectory (Hryniewicz 2012, Section 7).
--
--   **Formalization Note** $\mathrm{pr}_S\circ U$ is `pageMap H U`, with `proj H` the radial projection; $C^1$ on the set is `ContDiffOn ℝ 1 _ (I ×ˢ Set.univ)`.
-- source:
--   General lemma; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Lemma 7.2

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- If `U` is `C¹` on `I × ℂ` (`I` open) and does not vanish there, then
`pageMap H U = proj H ∘ U` is `C¹` on `I × ℂ`. -/
theorem contDiffOn_pageMap (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (U : ℝ × ℂ → V 1) (I : Set ℝ) (hI : IsOpen I) (hU : ContDiffOn ℝ 1 U (I ×ˢ Set.univ))
    (hne : ∀ p ∈ I ×ˢ (Set.univ : Set ℂ), U p ≠ 0) :
    ContDiffOn ℝ 1 (pageMap H U) (I ×ˢ Set.univ) := by
  sorry

end FiniteEnergyPlane
