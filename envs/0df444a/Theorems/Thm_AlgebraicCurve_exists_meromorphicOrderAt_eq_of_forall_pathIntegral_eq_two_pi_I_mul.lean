-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_meromorphicOrderAt_eq_of_forall_pathIntegral_eq_two_pi_I_mul
-- name    : AlgebraicCurve.exists_meromorphicOrderAt_eq_of_forall_pathIntegral_eq_two_pi_I_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/3da0a13a-2774-508b-abc2-abb22766d7e8
-- title:
--   Meromorphic function realising the residue divisor of θ
-- statement:
--   Let $F$ be a field with a $\mathbb{C}$-algebra structure, assumed to contain an element $x$ transcendental over $\mathbb{C}$ such that $F$ is finite-dimensional over the intermediate field $\mathbb{C}(x)$, and assume `IsCurveOver ℂ F`: every nonzero $f \in F$ has a degree-zero divisor whose value at each place $v$ is $v.\mathrm{ord}\,f$, each residue field is finite over $\mathbb{C}$, and $\Omega[F\vert\mathbb{C}]$ is free of rank one over $F$. The set $\mathrm{Place}\,\mathbb{C}\,F$ of places (valuation subrings of $F$ containing $\mathbb{C}$, proper and principal) is equipped with a topology, a $\mathbb{C}$-charted structure and an analytic manifold structure, and is assumed Hausdorff and connected. It is assumed (hypothesis `hF`) that for every nonzero $f \in F$ and every place $v$ the chart reading $z \mapsto \mathrm{evalAt}_{\varphi_v^{-1}(z)}(f)$ is meromorphic at the centre $\varphi_v(v)$, of meromorphic order exactly $v.\mathrm{ord}\,f$, where $\varphi_v$ is the extended chart at $v$ and $\mathrm{evalAt}$ is evaluation at a place (the residue of $f$ pulled back to $\mathbb{C}$ when $f$ lies in the valuation ring, and $0$ otherwise). Let $D$ be a divisor, i.e. a finitely supported function $\mathrm{Place}\,\mathbb{C}\,F \to \mathbb{Z}$, and let $\theta \in \Omega[F\vert\mathbb{C}]$. Writing $\theta = h_v \cdot \mathrm{dCoord}_v$ with $\mathrm{dCoord}_v = \mathrm{d}\pi_v$ for the chosen uniformizer, with $h_v = v.\mathrm{differentialCoeff}\,\theta$, assume $-1 \le v.\mathrm{ord}\,h_v$ for every $v$ (at worst simple poles), and that the residue condition $\mathrm{evalAt}_v(\pi_v h_v) = D(v)$ holds at every $v$, where $\pi_v = v.\mathrm{dCoordFn}$ is the chosen element of order one with $\mathrm{d}\pi_v = \mathrm{dCoord}_v$. Assume finally that for every place $P$ and every loop $\gamma$ at $P$ with $D(\gamma(t)) = 0$ for all $t$, the path integral `pathIntegral θ γ` (defined as $g(1) - g(0)$ for a primitive $g$ of $\theta$ along $\gamma$ when one exists, and $0$ otherwise) equals $2\pi i m$ for some integer $m$. Then there exists a function $g : \mathrm{Place}\,\mathbb{C}\,F \to \mathbb{C}$ such that for every place $v$ the chart reading $z \mapsto g(\varphi_v^{-1}(z))$ is meromorphic at $\varphi_v(v)$ with meromorphic order equal to $D(v)$.
--
--   This is the analytic half of the sufficiency direction of Abel's theorem: a differential with at worst simple poles, residue divisor $D$ and all periods in $2\pi i \mathbb{Z}$ yields the function $\exp\left(\int \theta\right)$ whose chartwise orders are prescribed by $D$. The conclusion produces only a function on the set of places that is meromorphic in every chart, not yet an element of $F$; passing from it to principality of $D$ is done in [`AlgebraicCurve.Divisor.isPrincipal_of_forall_pathIntegral_eq_two_pi_I_mul`](thm.html#AlgebraicCurve.Divisor.isPrincipal_of_forall_pathIntegral_eq_two_pi_I_mul), which cites this statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_meromorphicOrderAt_eq_of_forall_pathIntegral_eq_two_pi_I_mul.lean

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

theorem AlgebraicCurve.exists_meromorphicOrderAt_eq_of_forall_pathIntegral_eq_two_pi_I_mul
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (D : Divisor ℂ F) (θ : Ω[F⁄ℂ]) (hθ : ∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ)
    (hres : ∀ v : Place ℂ F, Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) = (D v : ℂ))
    (hper : ∀ (P : Place ℂ F) (γ : Path P P), (∀ t, D (γ t) = 0) →
      ∃ m : ℤ, pathIntegral θ γ = 2 * Real.pi * Complex.I * m) :
    ∃ g : Place ℂ F → ℂ, ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) v).symm z))
          (extChartAt 𝓘(ℂ, ℂ) v v) = (D v : WithTop ℤ) := by sorry
