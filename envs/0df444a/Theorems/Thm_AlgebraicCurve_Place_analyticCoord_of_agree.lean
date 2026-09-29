-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_analyticCoord_of_agree
-- name    : AlgebraicCurve.Place.analyticCoord_of_agree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/96cc47b4-3e4d-5a4f-9a62-3cddf9a6cc08
-- title:
--   Unramified reading of f gives an analytic local coordinate
-- statement:
--   Let $F$ be a field that is an algebra over $\mathbb{C}$ and a curve over $\mathbb{C}$ in the sense of `IsCurveOver`: principal divisors exist (every $g \neq 0$ has a degree-zero divisor with multiplicities $v.\mathrm{ord}\,g$), every place has residue field finite over $\mathbb{C}$, and $\Omega[F/\mathbb{C}]$ is free of rank one over $F$. Here a place is a valuation subring of $F$ containing $\mathbb{C}$, proper, and a principal ideal ring, and $v.\mathrm{ord}$ is minus the logarithm of its associated adic valuation. The set $\mathrm{Place}\,\mathbb{C}\,F$ is assumed to carry a Hausdorff topology and a charted space structure modelled on $\mathbb{C}$. Two global hypotheses are imposed: $(hF)$ for every $g \neq 0$ in $F$ and every place $v$, the function $z \mapsto \mathrm{evalAt}_{(\mathrm{extChartAt}\;v)^{-1}(z)}(g)$ is meromorphic at $\mathrm{extChartAt}\;v\,(v)$ with meromorphic order equal to $v.\mathrm{ord}\,g$; and $(hrat)$ every place is rational, i.e. $\mathbb{C}$ surjects onto its residue field, so that $\mathrm{evalAt}$ returns the residue-field value in $\mathbb{C}$ for elements of the valuation subring, and $0$ otherwise. Let $f \in F$ be transcendental over $\mathbb{C}$, and let $\zeta$ be an open partial homeomorphism from $\mathrm{Place}\,\mathbb{C}\,F$ to $\mathbb{C}$ that reads $f$ on its source: $\zeta Q = \mathrm{evalAt}_Q(f)$ for all $Q$ in the source. Let $P$ be a place in the source of $\zeta$ with $f$ in its valuation subring and with $P.\mathrm{ord}\bigl(f - \mathrm{evalAt}_P(f)\bigr) = 1$. Then $\zeta \circ (\mathrm{extChartAt}\;P)^{-1}$ is analytic at $\mathrm{extChartAt}\;P\,(P)$ and its derivative there is nonzero.
--
--   This is the statement that, at a point where the function $f$ attains its value to order exactly one, a partial homeomorphism reading $f$ is a genuine analytic local coordinate compatible with the given chart — the unbranched case of the local normal form for holomorphic maps of Riemann surfaces. It is used in the construction of a paired cell family ([`AlgebraicCurve.exists_pairedCellFamily`](thm.html#AlgebraicCurve.exists_pairedCellFamily)), where such coordinates supply the grid on which the cells are cut.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_analyticCoord_of_agree.lean

import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff
open AlgebraicCurve

theorem AlgebraicCurve.Place.analyticCoord_of_agree {F : Type*} [Field F] [Algebra ℂ F]
    [IsCurveOver ℂ F] [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [T2Space (Place ℂ F)]
    (hF : ∀ g : F, g ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord g : WithTop ℤ))
    (hrat : ∀ P : Place ℂ F, P.IsRational)
    {f : F} (hf : Transcendental ℂ f)
    (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ)
    (hread : ∀ Q ∈ ζ.source, ζ Q = Place.evalAt Q f)
    (P : Place ℂ F) (hP : P ∈ ζ.source)
    (hfP : f ∈ P.toValuationSubring)
    (hord : P.ord (f - algebraMap ℂ F (P.evalAt f)) = 1) :
    AnalyticAt ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ∧
    deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ≠ 0 := by sorry
