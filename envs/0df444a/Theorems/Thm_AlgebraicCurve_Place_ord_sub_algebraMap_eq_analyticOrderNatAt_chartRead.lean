-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ord_sub_algebraMap_eq_analyticOrderNatAt_chartRead
-- name    : AlgebraicCurve.Place.ord_sub_algebraMap_eq_analyticOrderNatAt_chartRead
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/5a019d41-6d45-51ca-94a1-945baf771704
-- title:
--   Valuation at w as zero order of the chart-read function
-- statement:
--   Let $F$ be a field that is an algebra over $\mathbb{C}$ and satisfies `IsCurveOver ℂ F`: every nonzero $f \in F$ has a degree-zero divisor whose value at each place is $\operatorname{ord}_v f$, each residue field $v$.`ResidueField` is finite over $\mathbb{C}$, and $\Omega[F/\mathbb{C}]$ is free of rank one over $F$. Here a place is a valuation subring of $F$ containing the image of $\mathbb{C}$, distinct from $F$ itself and a principal ideal ring, $\operatorname{ord}_v f$ is minus the logarithm of the associated height-one-spectrum valuation of $f$, and `Place.evalAt v f` is the preimage in $\mathbb{C}$ of the residue of $f$ when $f$ lies in the valuation subring and $0$ otherwise. Assume the set of places carries a Hausdorff topology, a charted space structure over $\mathbb{C}$ and an analytic manifold structure for the model $𝓘(ℂ, ℂ)$, and assume the compatibility hypothesis `hF`: for every $f \neq 0$ and every place $v$, the function $z \mapsto$ `Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f` is meromorphic at the chart image $z_v(v)$ of the centre, with meromorphic order there equal to $\operatorname{ord}_v f$. Let $v, w$ be places with $w$ in the source of the extended chart $z_v$ at $v$, let $f \in F$ lie in the valuation subring of $w$, and let $t \in \mathbb{C}$ with $f - t \neq 0$ in $F$. Then the analytic order of $z \mapsto$ `v.chartRead f z` $- t$, i.e. of $z \mapsto$ `Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f` $- t$, at the point $z_v(w)$ is not $\top$, and $\operatorname{ord}_w(f - t)$ equals that analytic order, taken as a natural number and viewed in $\mathbb{Z}$.
--
--   This is the dictionary between valuations of $F$ at the points of a single chart and vanishing multiplicities of the corresponding holomorphic function of one complex variable: within the chart at $v$, the valuation $\operatorname{ord}_w(f-t)$ is exactly the multiplicity of $z_v(w)$ as a zero of the chart-read function minus $t$. It is used in the construction of the Abel–Jacobi map for the curve, where multiplicities of the solutions of $\mathrm{read} = t$ inside a chart disc must be identified with place-theoretic orders.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ord_sub_algebraMap_eq_analyticOrderNatAt_chartRead.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
open scoped Manifold ContDiff

theorem AlgebraicCurve.Place.ord_sub_algebraMap_eq_analyticOrderNatAt_chartRead
    (F : Type*) [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [T2Space (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (v w : Place ℂ F) (hw : w ∈ (extChartAt 𝓘(ℂ, ℂ) v).source) {f : F}
    (hf : f ∈ w.toValuationSubring) (t : ℂ) (hne : f - algebraMap ℂ F t ≠ 0) :
    analyticOrderAt (fun z => v.chartRead f z - t) (extChartAt 𝓘(ℂ, ℂ) v w) ≠ ⊤ ∧
      w.ord (f - algebraMap ℂ F t) =
        (analyticOrderNatAt (fun z => v.chartRead f z - t) (extChartAt 𝓘(ℂ, ℂ) v w) : ℤ) := by sorry
