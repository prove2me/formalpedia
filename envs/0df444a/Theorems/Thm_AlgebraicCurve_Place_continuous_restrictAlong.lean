-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_continuous_restrictAlong
-- name    : AlgebraicCurve.Place.continuous_restrictAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/040d5890-62bc-5ce7-9667-e9054637b142
-- title:
--   Continuity of place restriction along an integral map
-- statement:
--   Let $F$ and $F'$ be fields equipped with $\mathbb C$-algebra structures, each satisfying `IsCurveOver ℂ`: every nonzero element has a degree-zero divisor recording its orders at all places, every place has residue field finite-dimensional over $\mathbb C$, and $\Omega[F\!\mid\!\mathbb C]$ is free of rank one (likewise for $F'$). Here a place of $F$ over $\mathbb C$ is a valuation subring of $F$ containing $\mathbb C$, distinct from $F$ itself, and a principal ideal ring; $\operatorname{ord}_v f$ is minus the logarithm of the associated $\mathbb Z^{m0}$-valued adic valuation, and $\operatorname{ev}_v(f)$ is the preimage in $\mathbb C$ of the residue class of $f$ when $f$ lies in the valuation subring, and $0$ otherwise. Assume the set of places of $F$ carries a topology and an atlas of $\mathbb C$-charts for which it is compact Hausdorff, and the set of places of $F'$ carries a topology and an atlas of $\mathbb C$-charts for which it is Hausdorff. Assume compatibility of these structures with the fields: for each nonzero $f \in F$ and each place $v$, the function $z \mapsto \operatorname{ev}_{(\mathrm{extChartAt}\,v)^{-1}(z)}(f)$ is meromorphic at the chart centre $\mathrm{extChartAt}\,v\,(v)$ with meromorphic order there equal to $\operatorname{ord}_v f$, and the same for each nonzero $f \in F'$ at each place $w$ of $F'$. Then for every $\mathbb C$-algebra homomorphism $\varphi\colon F \to F'$ whose underlying ring homomorphism is integral, the map sending a place $w$ of $F'$ to its restriction along $\varphi$, namely the place of $F$ whose valuation subring is the preimage of that of $w$ under $\varphi$, is continuous.
--
--   This is the continuity of the map of Riemann surfaces $X' \to X$ induced by an integral inclusion of function fields in one variable over $\mathbb C$, in the place-theoretic model of the surfaces. It is used in the construction of correspondences and in the Abel–Jacobi estimates, being cited by [`AlgebraicCurve.exists_ball_abelJacobiDiv_correspondence_sub_sub_mem_pathPeriodLattice`](thm.html#AlgebraicCurve.exists_ball_abelJacobiDiv_correspondence_sub_sub_mem_pathPeriodLattice) and [`AlgebraicCurve.exists_ball_abelJacobiVec_restrictAlong_sub_sub_mem_pathPeriodLattice`](thm.html#AlgebraicCurve.exists_ball_abelJacobiVec_restrictAlong_sub_sub_mem_pathPeriodLattice).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_continuous_restrictAlong.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
open scoped Manifold

theorem AlgebraicCurve.Place.continuous_restrictAlong
    (F F' : Type*) [Field F] [Algebra ℂ F] [Field F'] [Algebra ℂ F']
    [IsCurveOver ℂ F] [IsCurveOver ℂ F']
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [CompactSpace (Place ℂ F)] [T2Space (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    [TopologicalSpace (Place ℂ F')] [ChartedSpace ℂ (Place ℂ F')] [T2Space (Place ℂ F')]
    (hF' : ∀ f : F', f ≠ 0 → ∀ w : Place ℂ F',
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) w).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) w w) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) w).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) w w) = (w.ord f : WithTop ℤ))
    (φ : F →ₐ[ℂ] F') (hφ : φ.toRingHom.IsIntegral) :
    Continuous fun w : Place ℂ F' => w.restrictAlong φ hφ := by sorry
