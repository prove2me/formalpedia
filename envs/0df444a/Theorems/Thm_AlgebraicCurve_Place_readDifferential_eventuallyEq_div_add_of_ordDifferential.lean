-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_readDifferential_eventuallyEq_div_add_of_ordDifferential
-- name    : AlgebraicCurve.Place.readDifferential_eventuallyEq_div_add_of_ordDifferential
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/e33c3afe-c7d9-5184-abea-835359c69738
-- title:
--   Simple-pole expansion of a differential in a chart at a place
-- statement:
--   Let $F$ be a field equipped with a $\mathbb{C}$-algebra structure which is essentially of finite type and satisfies `IsCurveOver ℂ F`: every nonzero $f \in F$ has a degree-zero divisor whose value at each place $v$ is $v.\mathrm{ord}\,f = -\log$ of the $v$-adic valuation of $f$, each residue field $v.\mathrm{ResidueField}$ is finite over $\mathbb{C}$, and $\Omega[F/\mathbb{C}]$ is free of rank one over $F$; assume moreover that the set $\mathrm{Place}\,\mathbb{C}\,F$ of places carries a Hausdorff topology and a charted-space structure over $\mathbb{C}$. The hypothesis `hF` requires that for every nonzero $f \in F$ and every place $v$, writing $z_0 = \mathrm{extChartAt}\ \mathcal{I}(\mathbb{C},\mathbb{C})\ v\ v$ for the chart centre, the function $z \mapsto \mathrm{evalAt}_{\varphi_v^{-1}(z)}(f)$ is meromorphic at $z_0$ with meromorphic order exactly $v.\mathrm{ord}\,f$. Fix a place $v$ and $\theta \in \Omega[F/\mathbb{C}]$ with $-1 \le v.\mathrm{ordDifferential}\,\theta$, that is, $v.\mathrm{ord}$ of the coefficient $h = v.\mathrm{differentialCoeff}\,\theta$ (the chosen $h \in F$ with $\theta = h \cdot v.\mathrm{dCoord}$, where $v.\mathrm{dCoord} = D_{\mathbb{C}/F}(v.\mathrm{uniformizer})$, and $0$ if none exists) is at least $-1$. The conclusion: there is $G : \mathbb{C} \to \mathbb{C}$, analytic at $z_0$, such that for all $z$ in a punctured neighbourhood of $z_0$,
--   $$v.\mathrm{readDifferential}\,\theta\,(z) = \frac{\mathrm{evalAt}_v(\pi h)}{z - z_0} + G(z),$$
--   where $\pi = v.\mathrm{dCoordFn}$ is the element of $F$ selected by the existence assertion `exists_ord_eq_one_and_dCoord_eq` attached to $v$, $\mathrm{evalAt}_v$ denotes the value at $v$ (the preimage in $\mathbb{C}$ of the residue class, and $0$ off the valuation subring), and $v.\mathrm{readDifferential}\,\theta\,(z)$ is the product of $z \mapsto \mathrm{evalAt}_{\varphi_v^{-1}(z)}(h)$ with the derivative of $z \mapsto \mathrm{evalAt}_{\varphi_v^{-1}(z)}(\pi)$.
--
--   This is the local expansion, in a chart centred at a place $v$, of a differential with at worst a simple pole there: its chart coefficient differs from $\mathrm{evalAt}_v(\pi h)/(z-z_0)$ by a function analytic at the centre, so that the latter value is the residue in the simple-pole normalisation. It is used by [`AlgebraicCurve.coeffIn_local_calculus`](thm.html#AlgebraicCurve.coeffIn_local_calculus), and its proof cites `dCoordGenerates_of_isCurveOver` together with the analyticity of chart reads of elements of the valuation subring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_readDifferential_eventuallyEq_div_add_of_ordDifferential.lean

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

theorem AlgebraicCurve.Place.readDifferential_eventuallyEq_div_add_of_ordDifferential
    (F : Type*) [Field F] [Algebra ℂ F]
    [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (v : Place ℂ F) (θ : Ω[F⁄ℂ]) (hθ : -1 ≤ v.ordDifferential θ) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) v v),
        v.readDifferential θ z =
          Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) / (z - extChartAt 𝓘(ℂ, ℂ) v v) +
            G z := by sorry
