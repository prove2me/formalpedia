-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_pos_le_leaf_speed
-- name    : FiniteEnergyPlane.exists_pos_le_leaf_speed
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-25T15:29:17.126235+00:00
-- url     : https://prove2.me/theorems/8c3c2d4e-407a-403f-bce0-30e7ae0f1d25
-- title:
--   Reeb trajectories cross the leaves of a family with speed bounded below on compact sets
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level with Reeb field $R$. Let $U:\mathbb{R}\times\mathbb{C}\to\mathbb{R}^4\setminus\{0\}$ be a $C^1$ family and let $\Phi(\theta,z)$ be the point of $S$ on the ray through $U(\theta,z)$ (`pageMap H U`). Suppose that $D\Phi$ is injective at every point and that, at every point $p$, the vector $R(\Phi(p))$ is $D\Phi(p)(c,v)$ for some $c>0$ and $v\in\mathbb{C}$ (`IsReebPositiveAt`). Let $K$ be a compact subset of the image of $\Phi$.
--
--   Then there is $\varepsilon>0$ with the following property. If $y$ is a Reeb trajectory and $y(t)\in K$, there are a real function $f$ and a number $d\ge\varepsilon$ such that $f'(t)=d$ and, for all $s$ near $t$, the point $y(s)$ lies on the leaf $\Phi(\{f(s)\}\times\mathbb{C})$.
--
--   No injectivity of $\Phi$ and no periodicity in $\theta$ is assumed. Reusable for return and crossing statements about families of surfaces transverse to a Reeb flow.
--
--   **Formalization Note.** The function $f$ is defined on all of $\mathbb{R}$, but only its behaviour near $t$ is constrained. The number $\varepsilon$ depends on $K$ and $U$ only, not on $y$ or $t$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7.2.3

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `U : ℝ × ℂ → V 1` be a nowhere vanishing `C¹` family whose `pageMap H U` has injective
derivative and is positive against the Reeb field, and let `K` be a compact subset of the image of
`pageMap H U`. There is `ε > 0` such that, whenever a Reeb trajectory `y` is in `K` at time `t`, for
`s` near `t` the point `y s` lies on the leaf `pageMap H U (f s, ·)` for a real function `f` whose
derivative at `t` is at least `ε`. -/
theorem exists_pos_le_leaf_speed (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (U : ℝ × ℂ → V 1) (hU : ContDiff ℝ 1 U) (hne : ∀ p, U p ≠ 0)
    (hinj : ∀ p, Function.Injective (fderiv ℝ (pageMap H U) p))
    (hpos : ∀ p, IsReebPositiveAt H U p)
    (K : Set (V 1)) (hK : IsCompact K) (hKU : K ⊆ Set.range (pageMap H U)) :
    ∃ ε > 0, ∀ y : ℝ → V 1, IsReebTrajectory H y → ∀ t, y t ∈ K →
      ∃ (f : ℝ → ℝ) (d : ℝ), ε ≤ d ∧ HasDerivAt f d t ∧
        ∀ᶠ s in 𝓝 t, y s ∈ Set.range (fun z => pageMap H U (f s, z)) := by
  sorry

end FiniteEnergyPlane
