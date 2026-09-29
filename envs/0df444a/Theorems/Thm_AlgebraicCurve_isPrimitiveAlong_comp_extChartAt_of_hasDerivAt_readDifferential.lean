-- Prove2me | Theorems.Thm_AlgebraicCurve_isPrimitiveAlong_comp_extChartAt_of_hasDerivAt_readDifferential
-- name    : AlgebraicCurve.isPrimitiveAlong_comp_extChartAt_of_hasDerivAt_readDifferential
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/5934e5f2-da48-5971-816a-f3104c3999ed
-- title:
--   Chart primitives give primitives along paths inside a chart
-- statement:
--   Let $F$ be a field equipped with a $\mathbb{C}$-algebra structure, assume that some $x \in F$ is transcendental over $\mathbb{C}$ with $F$ finite-dimensional over the intermediate field $\mathbb{C}(x)$, and assume `IsCurveOver ℂ F`: every nonzero $f \in F$ has a degree-zero divisor whose value at each place $v$ is $v.\mathrm{ord}\,f$, every residue field of a place is finite over $\mathbb{C}$, and $\Omega_{F/\mathbb{C}}$ is free of rank one over $F$. Assume the set $\mathrm{Place}\;\mathbb{C}\;F$ of places carries a Hausdorff topology and a charted structure over $\mathbb{C}$ making it an analytic manifold, and assume the hypothesis `hF`: for each nonzero $f \in F$ and each place $v$, the chart reading $z \mapsto \mathrm{evalAt}\,((\mathrm{extChartAt}\;v)^{-1} z)\,f$ is meromorphic at $\varphi_v(v) := \mathrm{extChartAt}\;v\;v$ with meromorphic order there equal to $v.\mathrm{ord}\,f$. Let $\eta \in \Omega_{F/\mathbb{C}}$, let $v$ be a place, and let $U$ be an open set contained in the source of $\varphi_v$ such that for every $u \in U$ one has $0 \le u.\mathrm{ord}(u.\mathrm{differentialCoeff}\,\eta)$, and both $v.\mathrm{differentialCoeff}\,\eta$ (the chosen $h$ with $\eta = h \cdot v.\mathrm{dCoord}$) and the element `v.dCoordFn` of $F$ attached to $v$ lie in the valuation subring of $u$. Let $\Phi : \mathbb{C} \to \mathbb{C}$ satisfy, for every $u \in U$, $\mathrm{HasDerivAt}$ at $\varphi_v(u)$ with derivative $v.\mathrm{readDifferential}\,\eta\,(\varphi_v(u))$, that is the product of $\mathrm{evalAt}\,(\varphi_v^{-1}(z))(v.\mathrm{differentialCoeff}\,\eta)$ with the derivative at $z = \varphi_v(u)$ of $z \mapsto \mathrm{evalAt}\,(\varphi_v^{-1}(z))(v.\mathrm{dCoordFn})$. Then for every path $\gamma$ from a place $P$ to a place $Q$ with $\gamma(t) \in U$ for all $t$, the function $t \mapsto \Phi(\varphi_v(\gamma(t)))$ is a primitive of $\eta$ along $\gamma$: for each parameter $t_0$ there is $\Psi : \mathbb{C} \to \mathbb{C}$ which, for $z$ in a neighbourhood of $\varphi_{\gamma(t_0)}(\gamma(t_0))$, has derivative $(\gamma(t_0)).\mathrm{readDifferential}\,\eta\,(z)$ at $z$, and which satisfies $\Phi(\varphi_v(\gamma(t))) = \Psi(\varphi_{\gamma(t_0)}(\gamma(t)))$ for all $t$ near $t_0$.
--
--   This is the local-to-global comparison underlying path integration of differentials on the Riemann surface of places: a single primitive taken in one chart serves as a primitive along any path staying in the part of the chart domain where the coefficient and the chosen element at $v$ are regular, the change-of-chart transformation rule for the local coefficients of $\eta$ being what makes the two readings agree. It feeds the computation of period and residue integrals, being cited by [`AlgebraicCurve.exists_meromorphicOrderAt_eq_of_forall_pathIntegral_eq_two_pi_I_mul`](thm.html#AlgebraicCurve.exists_meromorphicOrderAt_eq_of_forall_pathIntegral_eq_two_pi_I_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_isPrimitiveAlong_comp_extChartAt_of_hasDerivAt_readDifferential.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
open scoped Manifold ContDiff Topology

theorem AlgebraicCurve.isPrimitiveAlong_comp_extChartAt_of_hasDerivAt_readDifferential
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [T2Space (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (η : Ω[F⁄ℂ]) (v : Place ℂ F) (U : Set (Place ℂ F)) (hU : IsOpen U)
    (hUv : U ⊆ (extChartAt 𝓘(ℂ, ℂ) v).source)
    (hηU : ∀ u ∈ U, 0 ≤ u.ordDifferential η)
    (hcoeff : ∀ u ∈ U, v.differentialCoeff η ∈ u.toValuationSubring)
    (hunif : ∀ u ∈ U, v.dCoordFn ∈ u.toValuationSubring)
    (Φ : ℂ → ℂ)
    (hΦ : ∀ u ∈ U, HasDerivAt Φ (v.readDifferential η (extChartAt 𝓘(ℂ, ℂ) v u))
      (extChartAt 𝓘(ℂ, ℂ) v u))
    {P Q : Place ℂ F} (γ : Path P Q) (hγ : ∀ t, γ t ∈ U) :
    IsPrimitiveAlong η γ (fun t => Φ (extChartAt 𝓘(ℂ, ℂ) v (γ t))) := by sorry
