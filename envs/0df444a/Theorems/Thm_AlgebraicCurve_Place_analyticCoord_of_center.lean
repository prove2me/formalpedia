-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_analyticCoord_of_center
-- name    : AlgebraicCurve.Place.analyticCoord_of_center
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/7032a0a7-2e7b-5181-838c-ae52ac4eef56
-- title:
--   Analyticity of a local coordinate in every chart of its domain
-- statement:
--   Let $F$ be a field that is an algebra over $\mathbb{C}$, and consider the set $\mathrm{Place}\,\mathbb{C}\,F$ of places of $F$ over $\mathbb{C}$, a place being a valuation subring of $F$ that contains the image of $\mathbb{C}$ under the structure map, is not all of $F$, and is a principal ideal ring. Assume this set is endowed with a topology, with a charted-space structure with model space $\mathbb{C}$, and with an analytic ($C^\omega$) manifold structure for the model with corners $\mathcal{I}(\mathbb{C},\mathbb{C})$. Fix a place $v$ and an open partial homeomorphism $\zeta$ from $\mathrm{Place}\,\mathbb{C}\,F$ to $\mathbb{C}$ whose source is contained in the source of the extended chart at $v$, such that the transported map $\zeta \circ (\mathrm{extChartAt}\ v)^{-1}$ is analytic on a neighbourhood of each point of the image of $\zeta$'s source under the extended chart at $v$, and has nowhere vanishing derivative on that image. Then for every place $P$ in the source of $\zeta$, the map $\zeta \circ (\mathrm{extChartAt}\ P)^{-1}$ is analytic at the point $(\mathrm{extChartAt}\ P)(P)$ and its derivative there is nonzero.
--
--   This is the standard chart-independence statement for local coordinates on a complex curve: being a local analytic coordinate with non-vanishing derivative is a condition independent of the chart in which it is read, because the chart transitions of an analytic manifold are biholomorphic. It is used as a step in the construction of a paired cell family ([`AlgebraicCurve.exists_pairedCellFamily`](thm.html#AlgebraicCurve.exists_pairedCellFamily)), where coordinates defined near one place must be recognised as coordinates near each point of their domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_analyticCoord_of_center.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff
open AlgebraicCurve

theorem AlgebraicCurve.Place.analyticCoord_of_center {F : Type*} [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] {v : Place ℂ F}
    (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ)
    (hsub : ζ.source ⊆ (extChartAt 𝓘(ℂ, ℂ) v).source)
    (han : AnalyticOnNhd ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm)
      (extChartAt 𝓘(ℂ, ℂ) v '' ζ.source))
    (hder : ∀ z ∈ extChartAt 𝓘(ℂ, ℂ) v '' ζ.source,
      deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm) z ≠ 0)
    (P : Place ℂ F) (hP : P ∈ ζ.source) :
    AnalyticAt ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ∧
    deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ≠ 0 := by sorry
