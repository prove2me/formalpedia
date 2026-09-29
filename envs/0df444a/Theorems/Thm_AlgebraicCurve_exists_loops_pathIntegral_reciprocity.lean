-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_loops_pathIntegral_reciprocity
-- name    : AlgebraicCurve.exists_loops_pathIntegral_reciprocity
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/b837202f-7a09-5eca-896e-a210298a5b85
-- title:
--   Canonical loops and Riemann's bilinear period relations
-- statement:
--   Let $F$ be a field with a $\mathbb{C}$-algebra structure, finitely generated in the sense that some $x \in F$ is transcendental over $\mathbb{C}$ with $F$ finite-dimensional over $\mathbb{C}(x)$; assume `IsCurveOver ℂ F` (principal divisors, each place having residue field finite over $\mathbb{C}$, and $\Omega[F\!\restriction\!\mathbb{C}]$ free of rank $1$ over $F$) and `HasCanonicalDivisor` (each nonzero $\omega$ has a finitely supported divisor $v \mapsto v.\mathrm{ordDifferential}\,\omega$). Assume the set of places $\mathrm{Place}\,\mathbb{C}\,F$, i.e. of proper valuation subrings of $F$ containing $\mathbb{C}$ that are principal ideal rings, carries a compact, Hausdorff, connected analytic one-dimensional complex manifold structure, and (`hF`) that for every $f \neq 0$ and every place $v$ the function read in the extended chart at $v$ is meromorphic at the chart image of $v$ with meromorphic order $v.\mathrm{ord}\,f$. Let $b$ be a $\mathbb{C}$-basis $(b_i)_{i \in \mathrm{Fin}\,n}$ of the regular differentials (those $\omega$ which at each $v$ equal $f \cdot v.\mathrm{dCoord}$ with $f$ in the valuation ring of $v$), $P_0$ a place and $S$ a finite set of places. Then there are base points $P\alpha_j, P\beta_j$ and loops $\alpha_j$ at $P\alpha_j$, $\beta_j$ at $P\beta_j$ ($j \in \mathrm{Fin}\,n$) such that: (i) no point of any $\alpha_j$ or $\beta_j$ lies in $S$ or equals $P_0$; (ii) for every place $Q$ and every loop $\delta$ at $Q$ there are integers $\kappa_j, \mu_j$ with $\int_\delta \xi = \sum_j (\kappa_j \int_{\alpha_j} \xi + \mu_j \int_{\beta_j} \xi)$ for all regular $\xi$; (iii) for every loop $\delta$ avoiding $S$ there are integers $\kappa_j, \mu_j$ and an integer-valued function $w$ on places such that every $\theta \in \Omega[F\!\restriction\!\mathbb{C}]$ with $v.\mathrm{ordDifferential}\,\theta \ge -1$ for all $v$ and $\ge 0$ for $v \notin S$ satisfies $\int_\delta \theta = \sum_j (\kappa_j \int_{\alpha_j} \theta + \mu_j \int_{\beta_j} \theta) + 2\pi i \sum_{v \in S} w(v)\, \mathrm{evalAt}_v(\mathrm{dCoordFn}_v \cdot \mathrm{differentialCoeff}_v \theta)$; (iv) $\sum_j (\int_{\alpha_j} \xi \int_{\beta_j} \xi' - \int_{\beta_j} \xi \int_{\alpha_j} \xi') = 0$ for all regular $\xi, \xi'$; and (v) for every divisor $E$ and every $\theta$ with $v.\mathrm{ordDifferential}\,\theta \ge -1$ for all $v$, with $\mathrm{evalAt}_v(\mathrm{dCoordFn}_v \cdot \mathrm{differentialCoeff}_v \theta) = E(v)$ for all $v$ and $E$ supported in $S$, there are integers $\kappa_j, \mu_j$, independent of $i$, with $\sum_j (\int_{\alpha_j} b_i \int_{\beta_j} \theta - \int_{\beta_j} b_i \int_{\alpha_j} \theta) = 2\pi i \bigl( (\mathrm{abelJacobiDiv}\,b\,P_0\,E)_i + \sum_j (\kappa_j \int_{\alpha_j} b_i + \mu_j \int_{\beta_j} b_i) \bigr)$ for every $i$. Here $\int_\gamma \omega$ is the path integral computed as the increment of a primitive of $\omega$ along $\gamma$ (zero if none exists), and $\mathrm{abelJacobiDiv}\,b\,P_0$ is the additive extension to divisors of $v \mapsto (\int_{\gamma} b_i)_i$ along a chosen path $\gamma$ from $P_0$ to $v$.
--
--   This packages the existence of a canonical homology basis of $2n$ loops on the compact Riemann surface of places of a complex function field together with Riemann's first bilinear relation and the reciprocity law between differentials of the first and third kinds. It is used in the description of the period lattice and of which Abel–Jacobi classes are realised by differences of path integrals of regular differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_loops_pathIntegral_reciprocity.lean

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
open scoped Manifold ContDiff

theorem AlgebraicCurve.exists_loops_pathIntegral_reciprocity
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] [HasCanonicalDivisor (K := ℂ) (F := F)]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    {n : ℕ} (b : Module.Basis (Fin n) ℂ ↥(regularDifferentials ℂ F)) (P₀ : Place ℂ F)
    (S : Finset (Place ℂ F)) :
    ∃ (Pα Pβ : Fin n → Place ℂ F) (α : ∀ j, Path (Pα j) (Pα j)) (β : ∀ j, Path (Pβ j) (Pβ j)),
      (∀ j t, α j t ∉ S ∧ α j t ≠ P₀ ∧ β j t ∉ S ∧ β j t ≠ P₀) ∧
      (∀ (Q : Place ℂ F) (δ : Path Q Q), ∃ κ μ : Fin n → ℤ,
        ∀ ξ ∈ regularDifferentials ℂ F,
          pathIntegral ξ δ =
            ∑ j, ((κ j : ℂ) * pathIntegral ξ (α j) + (μ j : ℂ) * pathIntegral ξ (β j))) ∧
      (∀ (Q : Place ℂ F) (δ : Path Q Q), (∀ t, δ t ∉ S) →
        ∃ (κ μ : Fin n → ℤ) (w : Place ℂ F → ℤ), ∀ θ : Ω[F⁄ℂ],
          (∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ) →
          (∀ v : Place ℂ F, v ∉ S → 0 ≤ v.ordDifferential θ) →
          pathIntegral θ δ =
            ∑ j, ((κ j : ℂ) * pathIntegral θ (α j) + (μ j : ℂ) * pathIntegral θ (β j)) +
              2 * Real.pi * Complex.I *
                ∑ v ∈ S, (w v : ℂ) * Place.evalAt v (v.dCoordFn * v.differentialCoeff θ)) ∧
      (∀ ξ ∈ regularDifferentials ℂ F, ∀ ξ' ∈ regularDifferentials ℂ F,
        ∑ j, (pathIntegral ξ (α j) * pathIntegral ξ' (β j) -
          pathIntegral ξ (β j) * pathIntegral ξ' (α j)) = 0) ∧
      (∀ (E : Divisor ℂ F) (θ : Ω[F⁄ℂ]),
        (∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ) →
        (∀ v : Place ℂ F, Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) = (E v : ℂ)) →
        (∀ v : Place ℂ F, E v ≠ 0 → v ∈ S) →
        ∃ κ μ : Fin n → ℤ, ∀ i : Fin n,
          ∑ j, (pathIntegral (b i : Ω[F⁄ℂ]) (α j) * pathIntegral θ (β j) -
              pathIntegral (b i : Ω[F⁄ℂ]) (β j) * pathIntegral θ (α j)) =
            2 * Real.pi * Complex.I *
              (abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ E i +
                ∑ j, ((κ j : ℂ) * pathIntegral (b i : Ω[F⁄ℂ]) (α j) +
                  (μ j : ℂ) * pathIntegral (b i : Ω[F⁄ℂ]) (β j)))) := by sorry
