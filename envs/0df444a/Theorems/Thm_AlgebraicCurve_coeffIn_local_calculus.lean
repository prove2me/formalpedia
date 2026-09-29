-- Prove2me | Theorems.Thm_AlgebraicCurve_coeffIn_local_calculus
-- name    : AlgebraicCurve.coeffIn_local_calculus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/89b99689-4ae8-5436-b504-20c72f34ac4c
-- title:
--   Local calculus for a differential's coefficient in an analytic chart
-- statement:
--   Let $F$ be a field with a $\mathbb{C}$-algebra structure which is a curve over $\mathbb{C}$ in the project's sense (every nonzero $f\in F$ has a degree-zero divisor given by its orders $v.\mathrm{ord}\,f$ at the places, every place has residue field finite over $\mathbb{C}$, and $\Omega[F/\mathbb{C}]$ is free of rank one over $F$), essentially of finite type over $\mathbb{C}$, and suppose the space $\mathrm{Place}\,\mathbb{C}\,F$ of places carries a Hausdorff topology and a charted structure over $\mathbb{C}$ making it an analytic manifold with model $\mathcal{I}(\mathbb{C},\mathbb{C})$. Assume: $hfg$, there is $x\in F$ transcendental over $\mathbb{C}$ with $F$ finite-dimensional over $\mathbb{C}(x)$; and $hF$, for every $f\neq 0$ and every place $v$ the function $z\mapsto \mathrm{evalAt}_{\varphi_v^{-1}(z)}(f)$ (with $\varphi_v=\mathrm{extChartAt}$ at $v$) is meromorphic at $\varphi_v(v)$ with meromorphic order exactly $v.\mathrm{ord}\,f$. Let $\zeta$ be an open partial homeomorphism from places to $\mathbb{C}$, $Q$ a place in its source such that $\zeta\circ\varphi_Q^{-1}$ is analytic at $\varphi_Q(Q)$ with nonzero derivative there, and $\theta\in\Omega[F/\mathbb{C}]$. Here $\mathrm{coeffIn}\ \zeta\ \theta\ w$ is $(\zeta^{-1}w).\mathrm{readDifferential}\,\theta$ evaluated at the chart coordinate of $\zeta^{-1}w$ in its own chart, times $\mathrm{deriv}(\varphi_{\zeta^{-1}w}\circ\zeta^{-1})(w)$, and $v.\mathrm{readDifferential}\,\theta\,z$ is the chart-read of the coefficient $v.\mathrm{differentialCoeff}\,\theta$ (the $f$ with $\theta=f\cdot v.\mathrm{dCoord}$, or $0$) at $z$ times the derivative at $z$ of the chart-read of $v.\mathrm{dCoordFn}$; also $Q.\mathrm{ordDifferential}\,\theta=Q.\mathrm{ord}(Q.\mathrm{differentialCoeff}\,\theta)$. The conclusion is a conjunction of two implications. First, if $0\le Q.\mathrm{ordDifferential}\,\theta$ then: for $w$ in a neighbourhood of $\zeta(Q)$, $\mathrm{coeffIn}\ \zeta\ \theta\ w = Q.\mathrm{readDifferential}\,\theta\,((\varphi_Q\circ\zeta^{-1})(w))\cdot \mathrm{deriv}(\varphi_Q\circ\zeta^{-1})(w)$; $\mathrm{coeffIn}\ \zeta\ \theta$ is analytic at $\zeta(Q)$; and for $y$ in a neighbourhood of $\varphi_Q(Q)$, $\mathrm{coeffIn}\ \zeta\ \theta\,((\zeta\circ\varphi_Q^{-1})(y))\cdot\mathrm{deriv}(\zeta\circ\varphi_Q^{-1})(y)=Q.\mathrm{readDifferential}\,\theta\,y$. Second, if $-1\le Q.\mathrm{ordDifferential}\,\theta$ then there is $G:\mathbb{C}\to\mathbb{C}$, analytic at $\zeta(Q)$, with $\mathrm{coeffIn}\ \zeta\ \theta\ w = \mathrm{evalAt}_Q(Q.\mathrm{dCoordFn}\cdot Q.\mathrm{differentialCoeff}\,\theta)/(w-\zeta(Q)) + G(w)$ for all $w$ in a punctured neighbourhood of $\zeta(Q)$.
--
--   This is the transformation law of a meromorphic $1$-form under an analytic change of local coordinate, together with the principal-part expansion at a point where the form has at worst a simple pole, the residue appearing as the value at $Q$ of $\mathrm{dCoordFn}\cdot\mathrm{differentialCoeff}$. It supplies the local input for the cell-dissection results on path integrals of differentials, where integrals along edges are compared with periods and with sums of residues.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_coeffIn_local_calculus.lean

import Definitions.Def_AlgebraicCurve_CellDissection
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Topology Real
open AlgebraicCurve Complex Set

universe u

theorem AlgebraicCurve.coeffIn_local_calculus
    (F : Type u) [Field F] [Algebra ℂ F] [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ) (Q : Place ℂ F) (hQ : Q ∈ ζ.source)
    (hζa : AnalyticAt ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q Q))
    (hζd : deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q Q) ≠ 0)
    (θ : Ω[F⁄ℂ]) :
    (0 ≤ Q.ordDifferential θ →
      (∀ᶠ w in 𝓝 (ζ Q), coeffIn ζ θ w =
        Q.readDifferential θ ((extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ.symm) w) *
          deriv (extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ.symm) w) ∧
      AnalyticAt ℂ (coeffIn ζ θ) (ζ Q) ∧
      ∀ᶠ y in 𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q),
        coeffIn ζ θ ((ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) y) *
            deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) y =
          Q.readDifferential θ y) ∧
    (-1 ≤ Q.ordDifferential θ →
      ∃ G : ℂ → ℂ, AnalyticAt ℂ G (ζ Q) ∧ ∀ᶠ w in 𝓝[≠] (ζ Q),
        coeffIn ζ θ w = Place.evalAt Q (Q.dCoordFn * Q.differentialCoeff θ) / (w - ζ Q) + G w) := by sorry
